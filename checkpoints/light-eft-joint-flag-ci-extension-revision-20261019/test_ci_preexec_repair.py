"""Real CIContext filesystem regressions; no compiler, lease or resource probe.

Tiny .olean contents exercise filesystem contracts only, never Lean decoding.
Run: python3 -I -S -B path/to/test_ci_preexec_repair.py
"""
from pathlib import Path
from contextlib import ExitStack
import ast, copy, io, json, os, sys, tempfile, unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
SPEC=json.loads((HERE/'ci-spec.json').read_text())
ENGINE=REPO/SPEC['engine_directory']
sys.path[:0]=[str(HERE),str(ENGINE),str(REPO/'scripts')]
import ci_gate, ci_inventory, ci_policy, ci_receipts, contracts, scope, child_runner

def put(path,data=b'fixture'):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data);return path

class Lease:
    file=None
    acquired_ns=1
    def __init__(self):self.checks=0
    def check(self):self.checks+=1

class Fixture:
    def __init__(self,stage='compile'):
        self.tmp=tempfile.TemporaryDirectory(prefix='ci-real-hook-')
        self.root=Path(self.tmp.name);self.work=self.root/'work';self.evidence=self.root/'runtime'
        self.work.mkdir();self.evidence.mkdir();(self.work/'objects').mkdir()
        self.project=self.root/'project';self.external=self.root/'external';self.tool=self.root/'tool'
        self.roots=[self.work/'objects',self.project,self.external,self.tool/'lib/lean']
        self.deps={}
        for row in SPEC['dependencies']:
            p=put(self.project/Path(*row['module'].split('.')).with_suffix('.olean'))
            self.deps[row['module']]=dict(contracts.bind(p),module=row['module'])
        self.bulk=put(self.external/'Mathlib/Test.olean',b'12345678')
        put(self.external/'Mathlib/Test.olean.private')
        self.metadata=put(self.external/'Mathlib/Test.trace')
        for name in sorted(ci_inventory.RUNTIME_SHARED):put(self.tool/'lib/lean'/name)
        put(self.tool/'lib/lean/Init.olean');put(self.tool/'lib/lean/libInit.a')
        for name in ['lean','leanchecker']:put(self.tool/'bin'/name)
        for row in SPEC['sources'].values():put(self.root/row['path'],b'-- source fixture\n')
        self.control=put(self.root/'control.json',b'{"fixture":true}\n')
        self.inv=ci_inventory.CIInventory(self.roots[1:],self.tool,contracts.bind)
        classified=self.inv.scan();self.inputs=dict(classified['semantic'])
        for p in [self.control,*(self.tool/'bin'/n for n in ['lean','leanchecker']),
                  *(self.root/row['path'] for row in SPEC['sources'].values())]:
            self.inputs[str(p)]=contracts.bind(p)
        import ci_text_fixture
        for rel in [ci_text_fixture.FIXTURE,ci_text_fixture.ORIGINAL,ci_text_fixture.COMPOSITE]:
            q=self.root/rel;q.write_bytes((REPO/rel).read_bytes());self.inputs[str(q)]=contracts.bind(q)
        self.commands=ci_policy.plans(self.root,self.tool,self.work,SPEC,self.roots,'a'*40)
        for p in self.commands:p['source_bindings']=[contracts.bind(s) for s in p['sources']]
        self.hashed=[]
        def tracked_bind(path,expected=None):
            self.hashed.append(str(path));return contracts.bind(path,expected)
        cls=ci_gate.context_type(scope.Context,self.work,self.evidence,self.commands,self.roots,self.deps,
                                 {'GITHUB_SHA':'a'*40},self.inputs,self.inv,classified,tracked_bind)
        self.lease=Lease();self.ctx=cls(self.lease);self.ctx.target.parent.mkdir(parents=True)
        index=ci_policy.STAGES.index(stage)
        # Simulated completed prefix, used solely to test the hook's file sets.
        if index:
            put(self.ctx.target,b'new object');self.ctx.new=contracts.object_outputs(self.roots[0],self.ctx.target,True)
        if index>=2:
            put(self.ctx.resolution,json.dumps(dict(target=contracts.TARGET,count=1,
                resolved=[dict(module=contracts.TARGET,object=str(self.ctx.target))],
                search_path=list(map(str,self.roots)))).encode())
            self.ctx.resolved={str(self.ctx.resolution):contracts.resolution(self.ctx.resolution,self.roots,self.ctx.target)}
        if index>=2:self.ctx.serialization_fixture_result={'simulated_prefix_for_filesystem_tests_only':True}
        self.ctx.seen=self.commands[:index];self.plan=self.commands[index]
        (self.evidence/stage).mkdir();self.record={}
        self.saves=0
    def close(self):self.tmp.cleanup()
    def save(self):self.saves+=1
    def prepare(self):
        accounting=type('Accounting',(),{'sample':lambda _:dict(system_available=8*1024**3)})()
        with patch.object(child_runner,'assert_idle'),patch.object(child_runner,'check_memory'),\
             patch.object(scope.shutil,'disk_usage',return_value=type('Disk',(),{'free':8*1024**3})()):
            self.ctx.before_child(self.plan,self.record,self.save)
            self.ctx.prepare_child(self.plan,self.record,self.save,accounting)
    def preexec(self):
        with patch.object(ci_gate.shutil,'disk_usage',return_value=type('Disk',(),{'free':8*1024**3})()):
            self.ctx.preexec(self.plan,self.record,self.save)

class RealHookTests(unittest.TestCase):
    def setUp(self):
        self.no_launch=ExitStack();self.addCleanup(self.no_launch.close)
        self.no_launch.enter_context(patch.object(child_runner.subprocess,'Popen',side_effect=AssertionError('No child allowed')))
        self.no_launch.enter_context(patch.object(child_runner,'run_child',side_effect=AssertionError('No launch allowed')))
    def fixture(self,stage='compile'):
        f=Fixture(stage);self.addCleanup(f.close);return f
    def test_actual_wiring_and_all_stage_hooks(self):
        self.assertIn('CIContext=context_type(scope.Context', (HERE/'ci_gate.py').read_text())
        for stage in ci_policy.STAGES:
            with self.subTest(stage=stage):
                f=self.fixture(stage);self.assertIn('preexec',type(f.ctx).__dict__)
                self.assertIs(type(f.ctx).verify,scope.Context.verify)
                f.prepare();f.hashed.clear()
                with patch.object(f.inv,'scan',side_effect=AssertionError('Full scan in preexec')),\
                     patch.object(scope,'effective',side_effect=AssertionError('Full selection in preexec')):
                    f.preexec()
                self.assertTrue(f.record['preexec_binding_verified'])
                self.assertEqual(set(f.hashed),set(f.ctx._critical))
                self.assertNotIn(str(f.bulk),f.hashed)
                self.assertIn(str(f.control),f.hashed)
                self.assertIn(f.ctx.input_ref['path'],f.hashed)
                self.assertIn(f.ctx.excluded_ref['path'],f.hashed)
                if stage!='compile':self.assertIn(str(f.ctx.target),f.hashed)
                if stage in ['replay','audit']:self.assertIn(str(f.ctx.resolution),f.hashed)
    def test_unprepared_and_mutated_plan_rejected(self):
        f=self.fixture()
        with self.assertRaises(ValueError):f.preexec()
        f.prepare();f.plan['argv'].append('--changed')
        with self.assertRaises(ValueError):f.preexec()
    def test_real_hook_mutations_rejected(self):
        def rewrite(p):p.write_bytes(b'87654321')
        def restored_mtime(f):
            st=f.bulk.stat();rewrite(f.bulk);os.utime(f.bulk,ns=(st.st_atime_ns,st.st_mtime_ns))
        def symlink(p):
            other=put(p.parent/(p.name+'.elsewhere'),p.read_bytes());p.unlink();p.symlink_to(other)
        def hardlink(f):os.link(f.bulk,f.root/'hardlink')
        def replace_parent(f):
            old=f.external/'Mathlib';old.rename(f.external/'moved');old.symlink_to(f.external/'moved',target_is_directory=True)
        mutations={
          'same-size semantic':lambda f:rewrite(f.bulk),
          'same-size restored mtime':restored_mtime,
          'semantic length':lambda f:f.bulk.write_bytes(b'changed length'),
          'missing semantic':lambda f:f.bulk.unlink(),
          'extra semantic':lambda f:put(f.external/'Mathlib/Extra.olean'),
          'extra empty directory':lambda f:(f.external/'empty').mkdir(),
          'missing directory':lambda f:(f.external/'Mathlib').rename(f.root/'moved'),
          'symlink semantic':lambda f:symlink(f.bulk),
          'symlink root':lambda f:(f.external.rename(f.root/'moved'),f.external.symlink_to(f.root/'moved',target_is_directory=True)),
          'symlink parent':replace_parent,
          'hardlink semantic':hardlink,
          'mode semantic':lambda f:f.bulk.chmod(0o600 if f.bulk.stat().st_mode&0o777!=0o600 else 0o644),
          'metadata same-size':lambda f:f.metadata.write_bytes(b'changed'),
          'critical source':lambda f:Path(f.plan['sources'][0]).write_bytes(b'-- source changed\n'),
          'critical executable':lambda f:(f.tool/'bin/lean').write_bytes(b'changed'),
          'input journal':lambda f:Path(f.ctx.input_ref['path']).write_bytes(b'changed'),
          'excluded journal':lambda f:Path(f.ctx.excluded_ref['path']).write_bytes(b'changed'),
          'submitted snapshot':lambda f:(f.ctx.stage_evidence/f.record['submitted_sources'][0]['snapshot']).write_bytes(b'changed'),
          'unexpected output':lambda f:put(f.ctx.target.parent/'Extra.olean'),
          'unexpected audit output':lambda f:put(f.ctx.audit/'extra'),
        }
        for name,mutate in mutations.items():
            with self.subTest(mutation=name):
                f=self.fixture();f.prepare();mutate(f)
                with self.assertRaises((ValueError,RuntimeError,OSError)):f.preexec()
        for stage,path in [('resolve','target'),('replay','resolution'),('audit','target')]:
            with self.subTest(stage=stage,path=path):
                f=self.fixture(stage);f.prepare();getattr(f.ctx,path).write_bytes(b'changed')
                with self.assertRaises((ValueError,RuntimeError,OSError)):f.preexec()
    def test_critical_hash_is_independent_of_stat_guard(self):
        f=self.fixture();f.prepare();f.control.write_bytes(b'{"fixture":false}')
        # Fault injection isolates the actual critical hash check.
        with patch.object(f.ctx._preexec_guard,'verify'):
            with self.assertRaises((ValueError,contracts.Rejected)):f.preexec()
    def test_receipt_replacement_is_allowed(self):
        f=self.fixture();f.prepare()
        receipt=put(f.ctx.stage_evidence/'receipt.tmp',b'updated receipt')
        os.replace(receipt,f.ctx.stage_evidence/'receipt.json');f.preexec()
        self.assertTrue(f.record['preexec_binding_verified'])
    def test_full_content_checks_remain_before_and_after(self):
        f=self.fixture();f.prepare()
        with patch.object(f.inv,'scan',wraps=f.inv.scan) as scan,\
             patch.object(scope,'unchanged',wraps=scope.unchanged) as unchanged:
            f.ctx.after_child(f.plan,{'exit':1},f.save)
            self.assertEqual(scan.call_count,1);self.assertGreaterEqual(unchanged.call_count,3)
        f.bulk.write_bytes(b'87654321')
        with self.assertRaises(contracts.Rejected):f.ctx.after_child(f.plan,{'exit':1},f.save)
        f=self.fixture();f.bulk.write_bytes(b'87654321')
        with self.assertRaises(contracts.Rejected):f.prepare()

class VirtualLog:
    def __init__(self,offset=0):self.offset=offset;self.rows=[]
    def tell(self):return self.offset
    def write(self,s):self.rows.append(s);self.offset+=len(s.encode())
    def flush(self):pass
    def fileno(self):raise AssertionError('No real fsync expected')

class TelemetryTests(unittest.TestCase):
    def setUp(self):
        self.stack=ExitStack();self.addCleanup(self.stack.close)
        self.stack.enter_context(patch.object(child_runner.exits,'probe',return_value=None))
        self.stack.enter_context(patch.object(child_runner.exits,'assess'))
        self.decision={'collection_errors':[],'accounting':{},'child':{},'sequence':0}
        self.stack.enter_context(patch.object(child_runner.telemetry,'collect',side_effect=lambda *a:copy.deepcopy(self.decision)))
        self.stack.enter_context(patch.object(child_runner.telemetry,'policy_errors',return_value=[]))
        self.stack.enter_context(patch.object(child_runner,'audit_output_errors',return_value=[]))
        self.kill=self.stack.enter_context(patch.object(child_runner,'kill_memory_group'))
    def sample(self,stage,log):
        record={'stage':stage}
        child_runner.runtime_sample(object(),{},None,None,record,lambda:None,log)
        return record
    def test_all_samples_persist_no_thinning(self):
        log=VirtualLog()
        for i in range(20):self.decision['sequence']=i;self.sample('audit',log)
        self.assertEqual([json.loads(s)['sequence'] for s in log.rows],list(range(20)))
    def test_audit_above_old_limit_only(self):
        log=VirtualLog(16*1024**2);self.sample('audit',log);self.assertEqual(len(log.rows),1)
        for stage in ['compile','resolve','replay']:
            with self.subTest(stage=stage):
                log=VirtualLog(16*1024**2)
                with self.assertRaises(child_runner.MemoryGuardError):self.sample(stage,log)
                self.assertEqual(log.rows,[])
    def test_exact_audit_boundary_then_failstop(self):
        size=len((json.dumps(self.decision,separators=(',',':'))+'\n').encode())
        log=VirtualLog(64*1024**2-size);self.sample('audit',log)
        self.assertEqual(log.tell(),64*1024**2)
        record={'stage':'audit'}
        with self.assertRaises(child_runner.MemoryGuardError):
            child_runner.runtime_sample(object(),{},None,None,record,lambda:None,log)
        self.assertEqual(len(log.rows),1);self.kill.assert_called_once()
        self.assertEqual(record['stop_decision_sample'],self.decision)
        self.assertEqual(record['latest_decision_sample'],self.decision)
        self.assertIn('exact sample retained',record['stop_decision_errors'][0])
    def test_receipt_bound_contract(self):
        for stage in ci_policy.STAGES:
            n=(64 if stage=='audit' else 16)*1024**2
            ci_receipts.decision_log_contract(stage,{'decision_log_bound_bytes':n},b'{}\n')
            for record,data in [({},b'{}\n'),({'decision_log_bound_bytes':n},b''),
                                ({'decision_log_bound_bytes':n},b'{}'),({'decision_log_bound_bytes':n+1},b'{}\n')]:
                with self.assertRaises(contracts.Rejected):ci_receipts.decision_log_contract(stage,record,data)
        class Oversize:
            def __bool__(self):return True
            def endswith(self,s):return True
            def __len__(self):return 64*1024**2+1
        with self.assertRaises(contracts.Rejected):
            ci_receipts.decision_log_contract('audit',{'decision_log_bound_bytes':64*1024**2},Oversize())
    def test_resource_limits_unchanged(self):
        self.assertEqual(child_runner.DEADLINE,90);self.assertEqual(child_runner.PREFLIGHT_DEADLINE,300)
        self.assertEqual(child_runner.INTERVAL,.1)
        self.assertEqual(child_runner.LIMITS['RLIMIT_CPU'],60)
        self.assertEqual(child_runner.LIMITS['RLIMIT_AS'],12*1024**3)
        self.assertEqual((child_runner.STOP_HEADROOM,child_runner.RSS_STOP,child_runner.ANON_GROWTH_STOP),
                         (1024**3,6*1024**3,3*1024**3))

class StaticTests(unittest.TestCase):
    def test_workflow_gate_before_global_replay_with_checks(self):
        text=(REPO/'.github/workflows/lean.yml').read_text()
        self.assertLess(text.index('id: light_eft_staged'),text.index('run: bash scripts/KernelCheck.sh'))
        self.assertIn('run: bash scripts/CheckModuleIndex.sh',text)
        self.assertIn('run: lake env lean scripts/AxiomAudit.lean',text)
        self.assertIn('timeout-minutes: 120',text)
        self.assertNotIn('continue-on-error:',text)
    def test_full_hooks_inherited_and_no_scope_preexec_delegation(self):
        tree=ast.parse((HERE/'ci_gate.py').read_text())
        cls=next(n for n in ast.walk(tree) if isinstance(n,ast.ClassDef) and n.name=='CIContext')
        names={n.name for n in cls.body if isinstance(n,ast.FunctionDef)}
        self.assertNotIn('verify',names);self.assertNotIn('finish',names)
        preexec=next(n for n in cls.body if isinstance(n,ast.FunctionDef) and n.name=='preexec')
        self.assertNotIn('super()',ast.unparse(preexec))
        self.assertNotIn('effective(',ast.unparse(preexec))

if __name__=='__main__':unittest.main(verbosity=2)
