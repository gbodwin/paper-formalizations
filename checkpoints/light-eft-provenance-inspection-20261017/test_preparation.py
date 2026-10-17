"""Python-only tests of prepared mapping/header parsing and frozen workflow guard."""
import hashlib,json,pathlib,unittest,yaml
from cache_mapping import imports,canonical_hash,hash_list,string_hash
BASE=pathlib.Path(__file__).resolve().parent

class MappingTests(unittest.TestCase):
    def test_nested_comments_and_order(self):
        self.assertEqual(imports('/- outer /- inner -/ -/\nmodule\npublic meta import all A.B\nimport C.D\n'),['A.B','C.D'])
    def test_documentation_ends_header(self):
        self.assertEqual(imports('import A\n/-! import Fake -/\nimport BodyOnly'),['A'])
    def test_commands_end_header(self):
        self.assertEqual(imports('import A\nnamespace B\nimport BodyOnly'),['A'])
    def test_comments_do_not_add_imports(self):
        self.assertEqual(imports('-- import Fake\nimport A\n/- import Nope -/\nimport B'),['A','B'])
    def test_unsupported_headers_refuse(self):
        for text in ['\timport A','import «escaped»','import A.β','public import A','/- unterminated']:
            with self.subTest(text=text),self.assertRaises(ValueError):imports(text)
    def test_canonical_crlf_not_lone_cr(self):
        self.assertEqual(canonical_hash(b'a\r\nb'),canonical_hash(b'a\nb'))
        self.assertNotEqual(canonical_hash(b'a\rb'),canonical_hash(b'a\nb'))
    def test_known_existing_archive_key_for_leaf(self):
        data=json.loads((BASE/'evidence/dependency-map.json').read_text())
        row=next(r for r in data['modules'] if r['module']=='Aesop.Script.Tactic')
        source=pathlib.Path(row['path']).read_bytes()
        self.assertEqual(hashlib.sha256(source).hexdigest(),row['source_sha256'])
        self.assertEqual(row['imports'],[])
        result=hash_list([int(data['root_hash'],16),hash_list(string_hash(x) for x in ['Aesop','Script','Tactic.lean']),canonical_hash(source)])
        self.assertEqual(f'{result:016x}','35a94f3f050967bd')
    def test_all_map_source_hashes_and_cache_filenames(self):
        data=json.loads((BASE/'evidence/dependency-map.json').read_text());self.assertEqual(len(data['modules']),3808)
        for row in data['modules']:
            self.assertEqual(hashlib.sha256(pathlib.Path(row['path']).read_bytes()).hexdigest(),row['source_sha256'])
            self.assertTrue((pathlib.Path('/workspace/cache/mathlib')/(row['cache_key']+'.ltar')).is_file())
    def test_workflow_guard_exact_and_dispatch_only(self):
        workflow=BASE.parent.parent/'.github/workflows/light-eft-exact.yml'
        data=yaml.load(workflow.read_text(),Loader=yaml.BaseLoader)
        self.assertEqual(set(data['on']),{'workflow_dispatch'})
        self.assertEqual(data['jobs']['verify']['if'],"inputs.source == '78cb40c7837db049d645d73696f2e0b724ce8a3b' && inputs.harness == 'ded293f2e4b17405cd009c5ba65acf913154b139'")
    def test_retained_workflows_have_no_autonomous_events(self):
        rows=json.loads((BASE.parent/'light-eft-clean-gate-review3-20261017/evidence/ci-workflow-definitions.json').read_text())
        self.assertEqual(len(rows),117)
        for row in rows:
            data=yaml.load(row['content'],Loader=yaml.BaseLoader)
            self.assertLessEqual(set(data['on']),{'push','pull_request','workflow_dispatch'})

if __name__=='__main__':unittest.main()
