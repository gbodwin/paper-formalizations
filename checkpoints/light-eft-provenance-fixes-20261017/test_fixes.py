"""Python-only source-derived fixtures; no Lean execution or runtime differential claim."""
import ast,hashlib,json,re,unittest
from pathlib import Path
from cache_mapping import imports,lean_char_is_whitespace
BASE=Path(__file__).resolve().parent
LEAN=Path('/workspace/toolchains/lean-4.34.0-linux/src/lean')
class FixTests(unittest.TestCase):
    def test_pinned_predicate_all_unicode_scalars(self):
        source=(LEAN/'Init/Data/Char/Basic.lean').read_text()
        body=source.split('def isWhitespace (c : Char) : Bool :=',1)[1].split('\n\n',1)[0]
        tokens=re.findall(r"c = ('(?:\\.|[^'])+')",body)
        self.assertEqual(len(tokens),4)
        expected={ast.literal_eval(t) for t in tokens}
        self.assertEqual(expected,{' ','\t','\r','\n'})
        for code in range(0x110000):
            if 0xD800<=code<=0xDFFF:continue
            c=chr(code)
            if lean_char_is_whitespace(c)!=(c in expected):self.fail(hex(code))
    def test_source_bound_tab_rejection(self):
        text=(LEAN/'Lean/Elab/ParseImportsFast.lean').read_text()
        self.assertIn("if curr == '\\t' then\n      s.mkError",text)
        self.assertIn('else if curr.isWhitespace then whitespace',text)
        for x in ['\timport A','import\tA','import A\timport B']:
            with self.subTest(x=x),self.assertRaises(ValueError):imports(x)
    def test_boundary_differential_fixtures(self):
        fixtures=json.loads((BASE/'boundary-fixtures.json').read_text())
        for f in fixtures:
            with self.subTest(f=f['name']):
                if f['candidate']=='REFUSE':
                    with self.assertRaises(ValueError):imports(f['input'])
                else:self.assertEqual(imports(f['input']),f['candidate'])
    def test_preserved_inputs_and_no_delete_flag(self):
        config=json.loads((BASE/'prepared-extraction-command.json').read_text())
        self.assertNotIn('--delete-corrupted',config['argv'])
        self.assertEqual(hashlib.sha256((BASE/config['stdin']).read_bytes()).hexdigest(),config['stdin_sha256'])
    def test_mapping_identical(self):
        old=BASE.parent/'light-eft-provenance-inspection-20261017/evidence/dependency-map.json'
        new=BASE/'evidence/dependency-map.json'
        self.assertEqual(new.read_bytes(),old.read_bytes())
        self.assertEqual(len(json.loads(new.read_text())['modules']),3808)
if __name__=='__main__':unittest.main(verbosity=2)
