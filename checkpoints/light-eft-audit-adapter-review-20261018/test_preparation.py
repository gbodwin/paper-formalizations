"""Synthetic contract/static checks only. No Lean, checker, child, or real audit."""
from pathlib import Path
from unittest.mock import patch
import ast, copy, hashlib, json, os, tempfile, unittest
import audit_context as context
import audit_contract as contract
import audit_outputs as outputs
import child_runner as runner
import pilot_child
import run_audit

A=Path(__file__).resolve().parent


class Tables(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='light-eft-audit-contract-',dir='/tmp')
        self.ci=Path(self.tmp.name)
        self.required=['LightEFTSpanners.Test']
        self.inv=[['LightEFTSpanners.Test','_private.Test.0.hidden','opaque','false','false']]
        self.dep=[['_private.Test.0.hidden','LightEFTSpanners.Test','opaque','propext','Nat.rec','false','false'],
                  ['propext','Init.Core','axiom','','','false','false'],
                  ['Nat.rec','Init.Prelude','recursor','','Nat','false','false'],
                  ['Nat','Init.Prelude','inductive','','Nat.zero','false','false'],
                  ['Nat.zero','Init.Prelude','constructor','','Nat','false','false']]
        self.loaded=['LightEFTSpanners.Test','LightEFTSpanners','Init.Core','Init.Prelude']
        self.summary='info: DIAGNOSTIC ONLY: 1 actual-owner project declarations, 1 covered declarations; 5 recursively visited constants, 1 opaque bodies; axioms [propext]\n'
    def tearDown(self):self.tmp.cleanup()
    def write(self):
        for name,header,rows in [('actual-owner-inventory.tsv',['owner','name','kind','unsafe','partial'],self.inv),
            ('recursive-dependencies.tsv',['name','owner','kind','typeDependencies','bodyDependencies','unsafe','partial'],self.dep)]:
            (self.ci/name).write_text('\t'.join(header)+'\n'+''.join('\t'.join(row)+'\n' for row in rows))
        (self.ci/'import-closure-loaded.txt').write_text('\n'.join(self.loaded)+'\n')
        (self.ci/'strict-violations.txt').write_text('\n')
    def validate(self):
        self.write();return contract.validate_tables(self.ci,self.required,self.summary)
    def test_private_opaque_recursion_and_recursor_cycle(self):
        self.assertEqual(self.validate()['visited_constants'],5)
    def test_missing_loaded_module(self):
        self.loaded.remove('LightEFTSpanners.Test')
        with self.assertRaisesRegex(RuntimeError,'Missing required'):self.validate()
    def test_duplicate_loaded_module(self):
        self.loaded.append('Init.Core')
        with self.assertRaisesRegex(RuntimeError,'duplicate loaded'):self.validate()
    def test_project_owned_generated_row_omitted(self):
        self.dep.append(['generated','LightEFTSpanners.Test','definition','','','false','false'])
        with self.assertRaisesRegex(RuntimeError,'omitted'):self.validate()
    def test_missing_root_from_closure(self):
        self.dep.pop(0)
        with self.assertRaisesRegex(RuntimeError,'root absent'):self.validate()
    def test_unsafe(self):
        self.dep[2][-2]='true'
        with self.assertRaisesRegex(RuntimeError,'Unsafe/partial'):self.validate()
    def test_partial(self):
        self.inv[0][-1]='true'
        with self.assertRaisesRegex(RuntimeError,'Unsafe/partial'):self.validate()
    def test_project_axiom(self):
        self.inv[0][2]='axiom';self.dep[0][2]='axiom'
        with self.assertRaisesRegex(RuntimeError,'Project axiom'):self.validate()
    def test_disallowed_recursive_axiom(self):
        self.dep[1][0]='sorryAx';self.dep[0][3]='sorryAx'
        with self.assertRaisesRegex(RuntimeError,'Disallowed recursive'):self.validate()
    def test_dangling_body_dependency(self):
        self.dep[0][4]='missing'
        with self.assertRaisesRegex(RuntimeError,'Unresolved'):self.validate()
    def test_dangling_type_dependency(self):
        self.dep[0][3]='missing'
        with self.assertRaisesRegex(RuntimeError,'Unresolved'):self.validate()
    def test_recursor_rules_missing(self):
        self.dep[2][4]=''
        with self.assertRaisesRegex(RuntimeError,'recursor-rule'):self.validate()
    def test_unreachable_export_row(self):
        self.dep.append(['unreachable','Init.Core','definition','','','false','false'])
        with self.assertRaisesRegex(RuntimeError,'not exactly'):self.validate()
    def test_historical_counts_not_substitute(self):
        self.summary=self.summary.replace('1 actual-owner','8950 actual-owner')
        with self.assertRaisesRegex(RuntimeError,'counts/axioms disagree'):self.validate()
    def test_strict_findings(self):
        self.write();(self.ci/'strict-violations.txt').write_text('recursive unsafe: x\n')
        with self.assertRaisesRegex(RuntimeError,'strict findings'):contract.validate_tables(self.ci,self.required,self.summary)
    def test_truncated_row(self):
        self.write();p=self.ci/'recursive-dependencies.tsv';p.write_bytes(p.read_bytes()[:-1])
        with self.assertRaisesRegex(RuntimeError,'Incomplete TSV'):contract.validate_tables(self.ci,self.required,self.summary)
    def test_duplicate_roots(self):
        self.inv.append(copy.deepcopy(self.inv[0]))
        with self.assertRaisesRegex(RuntimeError,'duplicate actual-owner'):self.validate()
    def test_duplicate_diagnostic(self):
        self.summary*=2
        with self.assertRaisesRegex(RuntimeError,'duplicate fresh'):self.validate()
    def test_only_preparation_defaults(self):
        with patch.object(run_audit,'execute',side_effect=AssertionError('Must not execute audit')):
            self.assertEqual(run_audit.main(['--describe']),0)
            with self.assertRaises(SystemExit):run_audit.main(['--execute-reviewed-audit'])


class OutputContract(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='light-eft-audit-outputs-',dir='/tmp')
        self.root=Path(self.tmp.name);self.work=self.root/'work';self.work.mkdir();ci=self.work/'ci-evidence';ci.mkdir()
        self.spec={'work':str(self.work),'work_identity':[self.work.stat().st_dev,self.work.stat().st_ino],
            'ci_identity':[ci.stat().st_dev,ci.stat().st_ino],'raw':str(self.root/'raw.log'),'created_wall_ns':0}
    def tearDown(self):self.tmp.cleanup()
    def complete(self):
        for name in outputs.OUTPUTS:(self.work/'ci-evidence'/name).write_text('synthetic fixture only\n')
        (self.root/'raw.log').write_text('synthetic raw fixture only\n')
    def test_empty_allowed_before_exec(self):self.assertEqual(outputs.inspect_outputs(self.spec)['source_directed_bytes'],0)
    def test_all_four_and_raw_required_after_exec(self):
        with self.assertRaisesRegex(RuntimeError,'Missing fresh'):outputs.inspect_outputs(self.spec,complete=True)
    def test_source_directed_budget_and_binding(self):
        self.complete();r=outputs.bind_outputs(self.spec);self.assertEqual(len(r['files']),5);self.assertLess(r['source_directed_bytes'],320*1024**2)
    def test_oversized_file(self):
        self.complete()
        with (self.root/'raw.log').open('r+b') as f:f.truncate(64*1024**2+1)
        with self.assertRaisesRegex(RuntimeError,'exceeds64MiB'):outputs.inspect_outputs(self.spec)
    def test_unexpected_working_file(self):
        (self.work/'extra').write_text('x')
        with self.assertRaisesRegex(RuntimeError,'Unexpected'):outputs.inspect_outputs(self.spec)
    def test_output_symlink(self):
        (self.work/'ci-evidence'/outputs.OUTPUTS[0]).symlink_to('/dev/null')
        with self.assertRaisesRegex(RuntimeError,'Unexpected/nonregular'):outputs.inspect_outputs(self.spec)
    def test_stale_output(self):
        self.complete();self.spec['created_wall_ns']=2**63
        with self.assertRaisesRegex(RuntimeError,'Stale'):outputs.inspect_outputs(self.spec,complete=True)
    def test_preexec_fresh_disk(self):
        fake=type('Usage',(),{'free':2*1024**3})()
        with patch.object(outputs.shutil,'disk_usage',return_value=fake):
            self.assertTrue(outputs.runtime_errors({'audit_output_budget':self.spec},preexec=True))
    def test_row_aligned_reconstruction(self):
        p=self.root/'synthetic.tsv';p.write_bytes(b'header\nrow1\n'+b'x'*42+b'\nrow3\n')
        result=contract.chunk_file(p,self.root/'chunks',target=20)
        data=b''.join((self.root/'chunks'/r['path']).read_bytes() for r in result['parts'])
        self.assertEqual(data,p.read_bytes());self.assertEqual(data.count(b'header\n'),1)
        self.assertTrue(all((self.root/'chunks'/r['path']).read_bytes().endswith(b'\n') for r in result['parts']))
        self.assertTrue(any(r['exceeds_target_single_row'] for r in result['parts']))


class StaticProfile(unittest.TestCase):
    def test_approved_lifecycle_and_limits(self):
        expected={'exit_transition.py':'1135140dd7dd3d075953d5d621f727a7a7c13796985c27da0c5afba68f95e76a',
                  'decision_telemetry.py':'08ae50f987ba67655e21d504e561ff5a23eda79104f35fe4c0d48e6e59de87fe'}
        for n,h in expected.items():self.assertEqual(hashlib.sha256((A/n).read_bytes()).hexdigest(),h)
        self.assertEqual(pilot_child.LIMITS,{'RLIMIT_AS':12*1024**3,'RLIMIT_CPU':60,'RLIMIT_FSIZE':64*1024**2,'RLIMIT_CORE':0})
        self.assertEqual(runner.DECISION_LOG_BOUND,16*1024**2)
        self.assertEqual((runner.RSS_STOP,runner.ANON_GROWTH_STOP,runner.STOP_HEADROOM,runner.DEADLINE),(6*1024**3,3*1024**3,1024**3,90.0))
    def test_exact_command_no_build_or_checker(self):
        self.assertEqual(context.exact_command(),context.PLAN['argv'])
        self.assertNotIn('-o',context.exact_command());self.assertNotIn('leanchecker',' '.join(context.exact_command()))
        self.assertEqual(len(context.PLAN['required_modules']),485)
        self.assertEqual(context.PLAN['resource_controls']['admission_visible'],4*1024**3)
    def test_every_adapter_python_parses(self):
        for p in A.glob('*.py'):ast.parse(p.read_text(),filename=str(p))


class FreshReceiptGate(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='light-eft-fresh-receipt-synthetic-',dir='/tmp')
        self.fake_adapter=Path(self.tmp.name)/'repo/checkpoints/adapter'
        self.evidence=self.fake_adapter/'executions/synthetic'
        self.evidence.mkdir(parents=True);(self.evidence/'attempt').mkdir()
        self.state={'attempts':1,'Lean_exec_authorized':True,'run_id':'synthetic','approved_adapter_commit':'0'*40,
                    'final_preservation':{'matching':True}}
        self.receipt={'source_commit':context.PLAN['source_commit'],'approved_adapter_commit':'0'*40,
                      'state':'finished','exit':0,'direct_reaped':False}
    def tearDown(self):self.tmp.cleanup()
    def invoke(self,evidence=None):
        E=evidence or self.evidence
        (E/'run-state.json').write_text(json.dumps(self.state))
        (E/'attempt/receipt.json').write_text(json.dumps(self.receipt))
        (E/'batch-lock.json').write_text('{}')
        with patch.object(contract,'__file__',str(self.fake_adapter/'audit_contract.py')):
            return contract.reconcile_run(E,context.PLAN)
    def test_historical_directory_not_fresh(self):
        E=self.fake_adapter/'historical';E.mkdir();(E/'attempt').mkdir()
        with self.assertRaisesRegex(RuntimeError,'fresh execution directory'):self.invoke(E)
    def test_final_preservation_required(self):
        self.state['final_preservation']['matching']=False
        with self.assertRaisesRegex(RuntimeError,'final preservation failed'):self.invoke()
    def test_nonzero_exit_rejected(self):
        self.receipt['exit']=1
        with self.assertRaisesRegex(RuntimeError,'Fresh zero-exit'):self.invoke()
    def test_exit_zero_without_owned_reaping_rejected(self):
        with self.assertRaisesRegex(RuntimeError,'Fresh zero-exit'):self.invoke()


if __name__=='__main__':unittest.main(verbosity=2)
