"""Filesystem/telemetry models only; all child, lease and resource mutations blocked."""
from pathlib import Path
import ast, contextlib, copy, fcntl, importlib.util, json, os, resource, subprocess, sys, tempfile, time, types, unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ENGINE = ROOT / 'checkpoints/light-eft-canonical-output-adapter-20261020'
sys.dont_write_bytecode = True
sys.path.insert(0, str(ENGINE)); sys.path.insert(0, str(HERE)); sys.path.insert(0, str(ROOT / 'scripts'))
import ci_gate, output_guards, prior_guard, same_run, audit_check
import bridge_fixture
from bridge_context import FocusedContext
from finite_contract import CONTRACT
from contracts import bind, tree
from ci_inventory import CIInventory

def forbidden(*args, **kwargs):
    raise AssertionError('Real process/lease/resource mutation forbidden in models')

def put(path, data=b'FILESYSTEM MODEL; NOT A LEAN OBJECT'):
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(data); return path

def account():
    return dict(namespace='model', membership='model', identities=['model'], headroom=8*1024**3,
        system_available=8*1024**3, nodes=[dict(path='/model', limit=str(16*1024**3), current=1,
        memory_stat={'anon':1}, oom={'oom':0}, pids_max='100', pids_current=1, pids_events={'max':0})])

class Models(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location('child_runner', ENGINE / 'child_runner.py')
        cls.runner = importlib.util.module_from_spec(spec); sys.modules['child_runner'] = cls.runner; spec.loader.exec_module(cls.runner)

    def setUp(self):
        self.block = contextlib.ExitStack(); self.addCleanup(self.block.close)
        for owner, name in [(subprocess, 'Popen'), (fcntl, 'flock'), (resource, 'setrlimit'),
                            (os, 'killpg'), (os, 'waitpid'), (os, 'waitid'), (os, 'wait4'), (os, 'fork'), (time, 'sleep')]:
            self.block.enter_context(patch.object(owner, name, side_effect=forbidden))

    def fixture(self, index=0):
        temp = tempfile.TemporaryDirectory(); self.addCleanup(temp.cleanup); base = Path(temp.name)
        root = base / 'light-eft-paid-joint-bridge-1-1'; work = root / 'work'; objects = work / 'objects'
        (objects / 'LightEFTPaidJointBridgeStage').mkdir(parents=True); (work / 'resolution').mkdir()
        evidence = root / 'runtime'; evidence.mkdir(); ordinary = base / 'ordinary'; ordinary.mkdir()
        identity = dict(GITHUB_SHA='a'*40, GITHUB_RUN_ID='1', GITHUB_RUN_ATTEMPT='1', GITHUB_EVENT_NAME='push', GITHUB_JOB='check')
        producers = [base / 'light-eft-paid-focused-1-1', base / 'light-eft-staged-1-1']
        for p in producers:
            (p / 'work/objects').mkdir(parents=True); (p / 'empty-directory').mkdir(); put(p / 'result.json', b'MODEL PRODUCER')
        spec = json.loads((HERE / 'ci-spec.json').read_text()); deps = {}
        for row in spec['dependencies']:
            m = row['module']; parent = producers[0] / 'work/objects' if row['origin']=='paid' else producers[1] / 'work/objects' if row['origin']=='decoder' else ordinary
            path = put(parent / Path(*m.split('.')).with_suffix('.olean')); deps[m] = dict(bind(path), module=m)
        roots = [objects, *(p / 'work/objects' for p in producers), ordinary]
        plans = ci_gate.build_plans(base / 'tool', work, spec, roots, identity['GITHUB_SHA'], bind)
        inventory = CIInventory(roots[1:], base / 'tool', bind); classified = inventory.scan(); inputs = dict(classified['semantic'])
        protected = {k:v for p in producers for k,v in tree(p).items()}; inputs.update(protected)
        for plan in plans:
            for source in plan['sources']: inputs[source] = bind(source)
        lock = put(root / 'MODEL-UNLOCKED-FD', b'').open('r+'); self.addCleanup(lock.close)
        lease = types.SimpleNamespace(file=lock, path=Path(lock.name), acquired_ns=1, check=lambda:None)
        ctx = FocusedContext(lease, work, evidence, plans, roots, deps, identity, inputs, inventory,
                             classified, prior_guard.capture(producers), protected)
        if index:
            path = put(ctx.target(CONTRACT['modules'][0])); ctx.new[str(path)] = bind(path)
        if index >= 2:
            path = put(work / 'resolution/SuppliedResponseJointBridge.json', b'MODEL COMPLETED RESOLUTION'); ctx.resolved[str(path)] = bind(path)
            # Model only: earlier successful resolve is now also a key fixture.
            ctx.bridge_fixture_result = bridge_fixture.validate_log(bridge_fixture.MARKER+'\n'+bridge_fixture.RESOLUTION_MARKER+'\n')
        ctx.seen = plans[:index]
        f = types.SimpleNamespace(base=base, root=root, work=work, ctx=ctx, plans=plans, plan=plans[index], producers=producers, identity=identity)
        self.prepare(f)
        return f

    def prepare(self, f):
        p = f.plan; (f.ctx.evidence / p['case'] / p['stage']).mkdir(parents=True)
        s = os.fstat(f.ctx.lock.fileno())
        f.record = dict(stage=p['stage'], argv=p['argv'], environment=p['env'], state='created',
            supervisor_pid=os.getpid(), deadline_seconds=90,
            lock=dict(fd=f.ctx.lock.fileno(), path=f.ctx.lock.name, device=s.st_dev, inode=s.st_ino))
        f.ctx.before_child(p, f.record, lambda:None)
        with patch.object(self.runner, 'assert_idle'), patch('bridge_context.shutil.disk_usage', return_value=types.SimpleNamespace(free=3*1024**3)):
            f.ctx.prepare_child(p, f.record, lambda:None, types.SimpleNamespace(sample=account))
        f.record.update(state='handshake-wait', child_pid=12345, runtime_wall_started_ns=time.monotonic_ns())

    def first_sample(self, f, rejected=False):
        now = time.monotonic_ns(); sample = dict(sample_utc='MODEL', sample_started_ns=now, sample_finished_ns=now+1,
            accounting=account(), child=dict(pid=12345,start_ticks=1,state='S',rss=1,vm=1,collection_errors=[]), collection_errors=[])
        def assess(child, s, r, before, descendants):
            s.update(exit_lifecycle={'terminal_confirmed':False}, observed_process_memory=dict(rss=1,vm=1))
        runner = self.runner
        with patch.object(runner.exits,'probe',return_value={'terminal':False}), patch.object(runner.exits,'assess',side_effect=assess), \
             patch.object(runner.telemetry,'collect',return_value=sample), patch.object(runner,'kill_memory_group') as kill, \
             patch.object(runner,'audit_output_errors',wraps=output_guards.runtime_errors) as guard:
            with tempfile.TemporaryFile(mode='w+') as log:
                if rejected:
                    with self.assertRaises(runner.MemoryGuardError): runner.runtime_sample(types.SimpleNamespace(pid=12345),account(),None,None,f.record,lambda:None,log)
                    kill.assert_called_once()
                else:
                    runner.runtime_sample(types.SimpleNamespace(pid=12345),account(),None,None,f.record,lambda:None,log); kill.assert_not_called()
            guard.assert_called_once_with(f.record,preexec=False,terminal=False)
        self.assertNotIn('handshake', f.record); self.assertNotIn('preexec_verified_ns', f.record)

    def test_first_handshake_sample_all_four_stages(self):
        for stage in range(4):
            with self.subTest(stage=stage): self.first_sample(self.fixture(stage))

    def test_prior_member_mutation_removal_extra_link_or_directory_reject_live(self):
        for mutation in ['bytes','remove','extra','symlink','hardlink','directory','index']:
            with self.subTest(mutation=mutation):
                f = self.fixture(); p = f.producers[0] / 'result.json'
                if mutation=='bytes': p.write_bytes(b'CHANGED')
                elif mutation=='remove': p.unlink()
                elif mutation=='extra': put(f.producers[0]/'new-file')
                elif mutation=='directory': (f.producers[0]/'new-empty').mkdir()
                elif mutation=='index': put(f.producers[1]/'evidence-sha256.json',b'CHANGED INDEX')
                elif mutation=='symlink': p.unlink(); p.symlink_to(put(f.base/'outside'))
                else: p.unlink(); os.link(put(f.base/'outside'),p)
                self.first_sample(f,True)

    def test_missing_completed_target_rejected_for_resolve_replay_audit(self):
        for stage in [1,2,3]:
            f=self.fixture(stage); f.ctx.target(CONTRACT['modules'][0]).unlink(); self.first_sample(f,True)

    def test_forbidden_outputs_and_resolution_symlinks_first_sample(self):
        for mutation in ['foreign','prefix','temporary','resolution','dangling','audit','sibling']:
            f=self.fixture(); target=f.ctx.target(CONTRACT['modules'][0]); path=f.work/'resolution/SuppliedResponseJointBridge.json'
            if mutation=='foreign': put(f.ctx.objects/'LightEFTPaidJointBridgeStage/Other.olean')
            elif mutation=='prefix': put(target.with_suffix('')/'Other.olean')
            elif mutation=='temporary': put(str(target)+'.tmp.12345')
            elif mutation=='resolution': put(path)
            elif mutation=='dangling': path.symlink_to(f.base/'missing')
            elif mutation=='audit': put(f.work/'audit/SuppliedResponseJointBridge/ci-evidence/strict-violations.txt')
            else: put(f.work/'foreign')
            self.first_sample(f,True)

    def test_real_preexec_accepts_unchanged_and_rejects_prior_mutation(self):
        for mutate in [False,True]:
            f=self.fixture()
            if mutate: (f.producers[1]/'result.json').write_bytes(b'CHANGED')
            with patch('bridge_context.shutil.disk_usage',return_value=types.SimpleNamespace(free=3*1024**3)):
                if mutate:
                    with self.assertRaises((RuntimeError,ValueError)): f.ctx.preexec(f.plan,f.record,lambda:None)
                else:
                    f.ctx.preexec(f.plan,f.record,lambda:None); self.assertTrue(f.record['preexec_binding_verified'])

    def test_full_context_rejects_prior_mutation_and_shadowed_input(self):
        for mutation in ['prior','shadow','masked']:
            f=self.fixture()
            if mutation=='prior': (f.producers[0]/'result.json').write_bytes(b'CHANGED')
            else:
                module=next(m for m in f.ctx.base_dependencies if m.startswith('LightEFTSpanners.'))
                path=f.ctx.objects/Path(*module.split('.')).with_suffix('.olean')
                if mutation=='shadow': put(path)
                else: path.parent.mkdir(parents=True,exist_ok=True)
            with self.assertRaises(RuntimeError): f.ctx.verify(f.plan)

    def test_compile_progression_preserves_both_producers_and_resolution(self):
        f=self.fixture(); before={p:bind(p) for p in f.ctx.prior_protected}
        put(f.ctx.target(CONTRACT['modules'][0])); put(f.ctx.evidence/f.plan['case']/'compile/raw.log',b'')
        f.record['exit']=0; f.ctx.after_child(f.plan,f.record,lambda:None)
        self.assertTrue(f.record['between_child_preservation_passed'])
        self.assertEqual(before,{p:bind(p) for p in before})
        f.plan=f.plans[1]; self.prepare(f); self.first_sample(f)
        self.assertIn(str(f.ctx.target(CONTRACT['modules'][0])),f.record['output_guard_spec']['protected'])

    def test_postchild_rejects_mutated_prior_and_completed_resolution(self):
        for mutation in ['prior','resolution']:
            f=self.fixture(2)
            if mutation=='prior': (f.producers[0]/'result.json').write_bytes(b'CHANGED')
            else: next(iter(map(Path,f.ctx.resolved))).write_bytes(b'CHANGED')
            f.record['exit']=0
            with self.assertRaises(RuntimeError): f.ctx.after_child(f.plan,f.record,lambda:None)

    def test_launcher_config_and_inherited_allocator_thread_stack_settings(self):
        f=self.fixture(); largest=0
        for p in f.plans:
            largest=max(largest,len(json.dumps(dict(argv=p['argv'],env=p['env'],stage=p['stage'])).encode()))
            self.assertEqual(p['env']['MIMALLOC_ARENA_RESERVE'],'128MiB'); self.assertEqual(p['env']['LEAN_NUM_THREADS'],'1')
            self.assertEqual(p['env']['LIGHTEFT_FROZEN_SOURCE_COMMIT'],'78cb40c7837db049d645d73696f2e0b724ce8a3b')
            if p['stage']=='replay':
                self.assertEqual(p['env']['LEAN_STACK_SIZE_KB'],'65536'); self.assertNotIn('MIMALLOC_VERBOSE',p['env'])
            else:
                self.assertEqual(p['env']['MIMALLOC_VERBOSE'],'1'); self.assertEqual(p['argv'][1:6],ci_gate.FLAGS)
        self.assertLessEqual(largest,4096)

    def test_launcher_config_under_full_normal_runner_roots(self):
        spec=json.loads((HERE/'ci-spec.json').read_text());repo=Path('/home/runner/work/paper-formalizations/paper-formalizations')
        temp=Path('/home/runner/work/_temp');tool=Path('/home/runner/.elan/toolchains/leanprover--lean4---v4.34.0')
        work=temp/'light-eft-paid-joint-bridge-39471963506-1/work'
        roots=[work/'objects',temp/'light-eft-paid-focused-39471963506-1/work/objects',temp/'light-eft-staged-39471963506-1/work/objects',repo/'.lake/build/lib/lean',
               *[repo/'.lake/packages'/n/'.lake/build/lib/lean' for n in spec['pins']],tool/'lib/lean']
        with patch.object(ci_gate,'ROOT',repo):
            plans=ci_gate.build_plans(tool,work,spec,roots,'a'*40,lambda p:{'path':str(p),'MODEL':True})
        self.assertEqual(len(plans),4)
        self.assertTrue(all(len(json.dumps(dict(argv=p['argv'],env=p['env'],stage=p['stage'])).encode())<=4096 for p in plans))
        self.assertIn(str(repo/spec['dependency_staged_roots'][0]),plans[0]['env']['LEAN_SRC_PATH'])

    def test_every_first_failure_stops_sequence_without_retry(self):
        f=self.fixture()
        for failure in range(4):
            calls=[]
            def child(p):
                calls.append(p)
                if len(calls)==failure+1: raise RuntimeError('MODEL FIRST FAILURE')
                return {'attempt_id':str(len(calls))}
            with self.assertRaises(RuntimeError): ci_gate.execute_four(f.plans,child,lambda:self.fail('finish after failure'))
            self.assertEqual(len(calls),failure+1)

    def test_singleton_contract_cannot_expand_to_fixtures_or_admissions(self):
        for mutation in ['fixtures','admission','module','completed']:
            f=self.fixture(); spec=f.record['output_guard_spec']
            if mutation=='fixtures':spec['focused']['mode']='fixtures'
            elif mutation=='admission':spec['admission_only']={}
            elif mutation=='module':spec['focused']['module']='Other'
            else:spec['focused']['completed_modules']=['Other']
            self.first_sample(f,True)

    def test_producer_contract_restores_bridge_authority_on_failure(self):
        original=sys.modules['finite_contract']; fake=types.ModuleType('MODEL')
        with self.assertRaises(ValueError):
            with same_run.producer_contract(fake):
                self.assertIs(sys.modules['finite_contract'],fake); raise ValueError('MODEL')
        self.assertIs(sys.modules['finite_contract'],original)

    def test_resolution_regular_and_dangling_absence_before_resolve(self):
        for dangling in [False,True]:
            f=self.fixture(1);p=f.work/'resolution/SuppliedResponseJointBridge.json'
            if dangling:p.symlink_to(f.base/'missing')
            else:put(p)
            with self.assertRaises(RuntimeError):f.ctx.before_child(f.plan,{},lambda:None)

    def test_only_verified_current_pid_can_authorize_compile_temporary(self):
        for correct in [False,True]:
            f=self.fixture();r=f.record;pid=12345
            r.update(state='exec-authorized',kernel_limits_verified=True,preexec_binding_verified=True,
                preexec_verified_ns=1,child_identity=dict(pid=pid,ppid=r['supervisor_pid'],sid=pid,pgid=pid,start_ticks=1),
                handshake=dict(pid=pid,ppid=r['supervisor_pid'],sid=pid,pgid=pid))
            put(str(f.ctx.target(CONTRACT['modules'][0]))+'.tmp.'+str(pid if correct else pid+1))
            errors=output_guards.runtime_errors(r)
            self.assertEqual(bool(errors),not correct)

    def test_bridge_schedule_reconciles_four_new_and_thirteen_prior_children(self):
        for mutation in ['none','duplicate','overlap','identity','lease','echild']:
            f=self.fixture();lease=dict(acquired_ns=101,state='released',kernel_echild=True)
            handoff=dict(prior_attempt_ids=['prior-%d'%i for i in range(13)],last_release_ns=100)
            for i,p in enumerate(f.plans):
                r=dict(CI_identity=f.identity,workflow_job='check',focused_module=p['module'],focused_case=p['case'],attempt_id='new-%d'%i,started_ns=110+i*10,ended_ns=115+i*10)
                if i==1:
                    raw=put(f.ctx.evidence/p['case']/p['stage']/'raw.log',(bridge_fixture.MARKER+'\n'+bridge_fixture.RESOLUTION_MARKER+'\n').encode())
                    r.update(state='finished',exit=0,completed_logs={'raw.log':bind(raw)},bridge_key_equivalence_fixture=bridge_fixture.validate_log(raw.read_text()))
                    if mutation=='duplicate':r['attempt_id']='prior-0'
                    elif mutation=='overlap':r['started_ns']=111
                    elif mutation=='identity':r['CI_identity']={}
                put(f.ctx.evidence/p['case']/p['stage']/'receipt.json',(json.dumps(r)+'\n').encode())
            if mutation=='lease':lease['acquired_ns']=100
            if mutation=='echild':lease['kernel_echild']=False
            verifier=unittest.mock.Mock()
            if mutation=='none':ci_gate.verify_schedule(f.plans,f.ctx.evidence,lease,f.ctx.base_dependencies,handoff,f.identity,verifier)
            else:
                with self.assertRaises(ValueError):ci_gate.verify_schedule(f.plans,f.ctx.evidence,lease,f.ctx.base_dependencies,handoff,f.identity,verifier)
            verifier.assert_called_once()

class HandoffModels(unittest.TestCase):
    setUp = Models.setUp

    def paid(self):
        temp=tempfile.TemporaryDirectory(); self.addCleanup(temp.cleanup); base=Path(temp.name)
        root=base/'light-eft-paid-focused-1-1'; root.mkdir()
        identity=dict(GITHUB_SHA='a'*40,GITHUB_RUN_ID='1',GITHUB_RUN_ATTEMPT='1',GITHUB_EVENT_NAME='push',GITHUB_JOB='check')
        normal=base/'normal'; normal.mkdir(); spec=json.loads((ROOT/same_run.PAID/'ci-spec.json').read_text())
        for row in spec['dependencies']: put(normal/Path(*row['module'].split('.')).with_suffix('.olean'))
        contract=same_run.module_at(ROOT/same_run.PAID/'finite_contract.py','MODEL_contract')
        policy=same_run.module_at(ROOT/same_run.PAID/'ci_gate.py','MODEL_policy')
        with same_run.producer_contract(contract): plans=policy.build_plans(base/'tool',root/'work',spec,[root/'work/objects',normal],identity['GITHUB_SHA'],bind)
        own={}
        for m in contract.CONTRACT['modules']:
            path=put(root/'work/objects'/Path(*m.split('.')).with_suffix('.olean')); own[m]=bind(path)
        def doc(rel,data): put(root/rel,(json.dumps(data,indent=2)+'\n').encode())
        lock=put(root/'ci-single-compiler.lock',b''); lock.chmod(0o600); s=lock.stat(); d=root.stat()
        kernel=dict(boot='MODEL-BOOT',namespaces={n:'MODEL-'+n for n in ['pid','mnt','cgroup']})
        lease=dict(path=str(lock),device=s.st_dev,inode=s.st_ino,directory_identity=[d.st_dev,d.st_ino],
            acquired_ns=1,release_ns=1000,state='released',kernel_echild=True,synthetic_fixture=False,historical_continuity=False,
            boot_id=kernel['boot'],namespace=kernel['namespaces'])
        doc('lease.json',lease); doc('production-claim.json',identity); doc('plans.json',plans)
        journal=(json.dumps(bind(next(normal.rglob('*.olean'))))+'\n').encode()
        audits={m:{'MODEL-AUDIT':m} for m in own}; stages=[]
        for i,p in enumerate(plans):
            r=dict(stage=p['stage'],focused_module=p['module'],focused_case=p['case'],CI_identity=identity,
                synthetic_fixture=False,dependency_qualification='NEWLY_OBSERVED_ORDINARY_CI_DEPENDENCIES; no historical object/provenance continuity',
                attempt_id=('%032x'%i),started_ns=10+i*10,ended_ns=15+i*10,state='finished',exit=0,
                outputs_after={'new_objects':list(own.values())[:(1 if i<4 else 2)]})
            doc('runtime/'+p['case']+'/'+p['stage']+'/receipt.json',r)
            put(root/'runtime'/p['case']/p['stage']/'raw.log',b'MODEL AUDIT LOG')
            stages.append(dict(module=p['module'],stage=p['stage'],attempt_id=r['attempt_id']))
        for case in ['PaidFlagSerialization','PaidFlagSampleComposition','PaidFlagFixtures']:
            put(root/'runtime'/case/'inputs.jsonl',journal)
            (root/'work/audit'/case/'ci-evidence').mkdir(parents=True)
        result=dict(accepted=True,CI_identity=identity,source_commit=identity['GITHUB_SHA'],harness_commit=identity['GITHUB_SHA'],
            dependency_qualification='Fresh ordinary-CI build objects; no historical preservation or authenticated clean cache provenance',
            stages=stages,result=dict(audits=audits,outputs={'new_objects':list(own.values())}))
        doc('result.json',result)
        f=types.SimpleNamespace(base=base,root=root,identity=identity,normal=[normal],tool=base/'tool',kernel=kernel,lease=lease,plans=plans,contract=contract,audits=audits,doc=doc)
        self.index(f); return f

    def index(self,f):
        rows=[dict(path=str(p.relative_to(f.root)),bytes=p.stat().st_size,sha256=__import__('hashlib').sha256(p.read_bytes()).hexdigest()) for p in sorted(f.root.rglob('*')) if p.is_file() and p.name!='evidence-sha256.json']
        f.doc('evidence-sha256.json',rows)

    def verify(self,f):
        original=same_run.module_at; calls=[]
        def loader(path,name):
            if name=='_bound_paid_auditor': return types.SimpleNamespace(validate=lambda ci,deps,raw,module:f.audits[module])
            return original(path,name)
        def four(evidence,lease,plans,deps,head,expected_source):
            self.assertEqual(len(plans),4); self.assertEqual(expected_source,head); self.assertIn(len(deps),[13,17]); calls.append(('four',len(deps)))
            for p in plans:
                r=json.loads((evidence/p['stage']/'receipt.json').read_text())
                if r['exit']!=0 or r['state']!='finished': raise ValueError('MODEL invalid receipt')
        def singleton(evidence,lease,plans,deps,head,expected_source):
            self.assertEqual(len(plans),1); self.assertEqual(len(deps),18); calls.append(('single',18))
        with patch.object(same_run,'module_at',side_effect=loader),patch.object(same_run,'kernel_context',return_value=f.kernel):
            result=same_run.verify_paid(ROOT,f.tool,{'RUNNER_TEMP':str(f.base)},f.identity,f.normal,four,singleton)
        self.assertEqual(calls,[('four',13),('four',17),('single',18)])
        return result

    def test_complete_paid_handoff_reconstructs_real_union_and_all_receipt_calls(self):
        f=self.paid(); result=self.verify(f)
        self.assertEqual(len(result['receipts']),9); self.assertEqual(len(result['objects']),2)
        self.assertEqual(result['prior_bindings'],same_run.prior_bindings((f.root/'runtime/PaidFlagFixtures/inputs.jsonl').read_text()))

    def test_paid_identity_lease_plan_receipt_and_union_negative_cases(self):
        mutations=['sha','run','attempt','event','job','claim','source','failed','boot','namespace','release','echild','lock',
                   'duplicate','overlap','module','exit','union','plan','journal','partial','foreign','index']
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                f=self.paid(); rel='result.json'; d=json.loads((f.root/rel).read_text())
                if mutation in ['sha','run','attempt','event','job']:
                    key={'sha':'GITHUB_SHA','run':'GITHUB_RUN_ID','attempt':'GITHUB_RUN_ATTEMPT','event':'GITHUB_EVENT_NAME','job':'GITHUB_JOB'}[mutation]
                    d['CI_identity'][key]='WRONG'
                elif mutation=='claim': rel='production-claim.json'; d={'wrong':'claim'}
                elif mutation=='source':d['source_commit']='b'*40
                elif mutation=='failed':d['accepted']=False
                elif mutation in ['boot','namespace','release','echild','lock']:
                    rel='lease.json'; d=json.loads((f.root/rel).read_text())
                    key={'boot':'boot_id','namespace':'namespace','release':'state','echild':'kernel_echild','lock':'inode'}[mutation]
                    d[key]=False if mutation=='echild' else {'changed':True} if mutation=='namespace' else 'WRONG'
                elif mutation in ['duplicate','overlap','module','exit','union']:
                    rel='runtime/PaidFlagSampleComposition/compile/receipt.json'; d=json.loads((f.root/rel).read_text())
                    if mutation=='duplicate':d['attempt_id']='%032x'%0
                    elif mutation=='overlap':d['started_ns']=11
                    elif mutation=='module':d['focused_module']='Other'
                    elif mutation=='exit':d['exit']=1
                    else:d['outputs_after']['new_objects']=d['outputs_after']['new_objects'][1:]
                elif mutation=='plan':rel='plans.json';d=[]
                elif mutation=='journal':
                    path=f.root/'runtime/PaidFlagSampleComposition/inputs.jsonl'; x=json.loads(path.read_text());x['sha256']='b'*64;path.write_text(json.dumps(x)+'\n')
                elif mutation=='partial':put(next((f.root/'work/objects').rglob('*.olean')).with_suffix('.olean.server'))
                elif mutation=='foreign':put(f.root/'work/objects/Foreign.olean')
                elif mutation=='index':put(f.root/'unindexed-file')
                if mutation not in ['journal','partial','foreign','index']:f.doc(rel,d)
                if mutation!='index':self.index(f)
                with self.assertRaises((RuntimeError,ValueError,KeyError)):self.verify(f)

    def test_retained_journal_membership_and_identity_reject_drift(self):
        f=self.paid(); row=bind(next(f.normal[0].rglob('*.olean'))); path=row['path']; old={'prior_bindings':{path:row},'retained_roots':list(map(str,f.normal))}
        for mutation in ['none','missing','added','changed']:
            semantic={path:copy.deepcopy(row)}; inputs=copy.deepcopy(semantic)
            if mutation=='missing':semantic={};inputs={}
            elif mutation=='added':semantic[str(f.normal[0]/'Other.olean')]=dict(row,path=str(f.normal[0]/'Other.olean'))
            elif mutation=='changed':semantic[path]['sha256']='b'*64;inputs=copy.deepcopy(semantic)
            if mutation=='none':same_run.retained_context(old,f.normal,semantic,inputs)
            else:
                with self.assertRaises(RuntimeError):same_run.retained_context(old,f.normal,semantic,inputs)

    def test_boundary_object_sources_missing_shadow_mask_source_drift(self):
        for mutation in ['none','missing','shadow','mask','source']:
            temp=tempfile.TemporaryDirectory();self.addCleanup(temp.cleanup);base=Path(temp.name)
            spec=json.loads((HERE/'ci-spec.json').read_text()); roots=[base/'.lake/packages'/n/'.lake/build/lib/lean' for n in ['aesop','mathlib']]
            semantic={}
            for row in spec['external_boundary_sources']:
                p=put(base/row['object']);semantic[str(p)]=bind(p);put(base/row['source'],b'MODEL SOURCE')
            row=spec['external_boundary_sources'][0]
            if mutation=='missing':(base/row['object']).unlink()
            elif mutation=='shadow':
                extra=base/'shadow';put(extra/'Aesop.olean');roots=[extra,*roots]
            elif mutation=='mask':
                extra=base/'mask';(extra/'Mathlib').mkdir(parents=True);roots=[extra,*roots]
            with patch.object(ci_gate,'ROOT',base),patch.object(ci_gate.subprocess,'check_output',return_value=b'WRONG' if mutation=='source' else b'MODEL SOURCE'):
                if mutation=='none':self.assertEqual(len(ci_gate.boundary_inputs(spec,roots,semantic,bind)),27)
                else:
                    with self.assertRaises(ValueError):ci_gate.boundary_inputs(spec,roots,semantic,bind)

    def test_finite_scope_rejects_wrong_equal_size_set_origins_proof_limits(self):
        good=json.loads((HERE/'ci-spec.json').read_text());ci_gate.finite_scope(good)
        for mutation in ['imports','origins','proof','limits','roots','count','order','boundary','pins','tool']:
            spec=copy.deepcopy(good)
            if mutation=='imports':spec['dependencies'][0]['module']='Other'
            elif mutation=='origins':
                a=next(x for x in spec['dependencies'] if x['origin']=='paid');b=next(x for x in spec['dependencies'] if x['origin']=='decoder');a['origin'],b['origin']=b['origin'],a['origin']
            elif mutation=='proof':next(x for x in spec['sources'] if x['role']=='bridge')['sha256']='b'*64
            elif mutation=='limits':spec['resource_contract']['cpu_seconds']['audit']=91
            elif mutation=='roots':spec['required_theorem_roots']=spec['required_theorem_roots'][:-1]
            elif mutation=='count':spec['project_modules_including_target']=80
            elif mutation=='order':spec['execution_order'].reverse()
            elif mutation=='boundary':spec['external_boundary_sources'][0]['module']='Other'
            elif mutation=='pins':spec['pins']['aesop']='b'*40
            else:spec['tool_hashes']['lean']='b'*64
            with self.assertRaises(ValueError):ci_gate.finite_scope(spec)

    def test_current_workflow_job_and_inherited_identity_checks(self):
        env=dict(GITHUB_ACTIONS='true',GITHUB_REPOSITORY='gbodwin/paper-formalizations',GITHUB_SHA='a'*40,
                 GITHUB_RUN_ID='1',GITHUB_RUN_ATTEMPT='1',GITHUB_EVENT_NAME='push',LEAN_NUM_THREADS='1',
                 GITHUB_REF='refs/heads/integration/light-eft-joint-flag-ci-20261019',GITHUB_JOB='check')
        # Existing accepted full/focused schedule identity, not the older
        # pre-split model that omitted actual workflow and role bindings.
        env.update(LIGHTEFT_VALIDATION_ROLE='full',LIGHTEFT_EXPECTED_SOURCE='a'*40,GITHUB_WORKFLOW='Lean',
            GITHUB_WORKFLOW_SHA='a'*40,GITHUB_WORKFLOW_REF=env['GITHUB_REPOSITORY']+'/.github/workflows/lean.yml@'+env['GITHUB_REF'],
            LIGHTEFT_JOB_WORKFLOW_REPOSITORY=env['GITHUB_REPOSITORY'],LIGHTEFT_JOB_WORKFLOW_PATH='.github/workflows/lean.yml',
            LIGHTEFT_JOB_WORKFLOW_SHA='a'*40,LIGHTEFT_JOB_WORKFLOW_REF=env['GITHUB_REPOSITORY']+'/.github/workflows/lean.yml@'+env['GITHUB_REF'])
        identity=ci_gate.workflow_identity(env,'a'*40);self.assertEqual(identity['GITHUB_JOB'],'check')
        focused=dict(env,LIGHTEFT_VALIDATION_ROLE='focused',LIGHTEFT_JOB_WORKFLOW_PATH='.github/workflows/light-eft-fair-bit-focused.yml',
            LIGHTEFT_JOB_WORKFLOW_REF=env['GITHUB_REPOSITORY']+'/.github/workflows/light-eft-fair-bit-focused.yml@'+env['GITHUB_REF'])
        self.assertEqual(ci_gate.workflow_identity(focused,'a'*40)['LIGHTEFT_VALIDATION_ROLE'],'focused')
        for key in ['GITHUB_JOB','GITHUB_SHA','GITHUB_ACTIONS','GITHUB_REPOSITORY','LEAN_NUM_THREADS','LIGHTEFT_VALIDATION_ROLE',
                    'LIGHTEFT_EXPECTED_SOURCE','GITHUB_WORKFLOW','GITHUB_WORKFLOW_REF','GITHUB_WORKFLOW_SHA',
                    'LIGHTEFT_JOB_WORKFLOW_PATH','LIGHTEFT_JOB_WORKFLOW_REPOSITORY','LIGHTEFT_JOB_WORKFLOW_SHA','LIGHTEFT_JOB_WORKFLOW_REF']:
            bad=dict(env);bad[key]='WRONG'
            with self.assertRaises(ValueError):ci_gate.workflow_identity(bad,'a'*40)

    def test_producer_pair_lease_order_and_attempt_identity(self):
        for mutation in ['none','lease','attempt','overlap']:
            f=self.paid();paid=self.verify(f);root=f.base/'light-eft-staged-1-1';root.mkdir()
            primary=put(root/'work/objects/LightEFTJointFlagSamplingStage/JointAssignmentLaw.olean')
            lock=put(root/'ci-single-compiler.lock',b'');lock.chmod(0o600);s=lock.stat();d=root.stat()
            lease=dict(f.lease,path=str(lock),device=s.st_dev,inode=s.st_ino,directory_identity=[d.st_dev,d.st_ino],acquired_ns=1100,release_ns=2000)
            if mutation=='lease':lease['acquired_ns']=999
            stages=[]
            for i,kind in enumerate(['compile','resolve','replay','audit']):
                r=dict(attempt_id='decoder-%d'%i,started_ns=1200+i*10,ended_ns=1205+i*10)
                if i==0 and mutation=='attempt':r['attempt_id']=paid['receipts'][0]['attempt_id']
                if i==0 and mutation=='overlap':r['started_ns']=20
                put(root/'runtime'/kind/'receipt.json',(json.dumps(r)+'\n').encode());stages.append(dict(stage=kind,attempt_id=r['attempt_id']))
            rows=[dict(path=str(p.relative_to(root)),bytes=p.stat().st_size,sha256=__import__('hashlib').sha256(p.read_bytes()).hexdigest()) for p in sorted(root.rglob('*')) if p.is_file()]
            put(root/'evidence-sha256.json',(json.dumps(rows)+'\n').encode())
            decoder=dict(root=root,lease=lease,stages=stages,item={'module':'LightEFTJointFlagSamplingStage.JointAssignmentLaw'},paths={'.olean':str(primary)},protected=same_run.indexed_evidence(root))
            with patch.object(same_run,'verify_paid',return_value=paid),patch.object(same_run,'verify_decoder',return_value=decoder),patch.object(same_run,'kernel_context',return_value=f.kernel):
                if mutation=='none':self.assertEqual(len(same_run.collect(ROOT,f.tool,{'RUNNER_TEMP':str(f.base)},f.identity,{},f.normal,None,None)['prior_attempt_ids']),13)
                else:
                    with self.assertRaises(RuntimeError):same_run.collect(ROOT,f.tool,{'RUNNER_TEMP':str(f.base)},f.identity,{},f.normal,None,None)

class AuditModels(unittest.TestCase):
    setUp=Models.setUp

    def audit(self):
        temp=tempfile.TemporaryDirectory();self.addCleanup(temp.cleanup);root=Path(temp.name)
        module=CONTRACT['modules'][0]; roots=CONTRACT['required_roots'][module]+['LightEFTSpanners.PaidJointBridge.'+n for n in ['edgeOrder','rawKeys','responses','storedHost','storedAssignment']]
        interfaces=CONTRACT['interfaces'][module]; imported={n:('LightEFTJointFlagSamplingStage.JointAssignmentLaw' if '.JointFlagSampling.' in n else 'LightEFTPaidSamplingStage.PaidFlagSerialization' if '.PaidFlagSerialization.' in n else 'LightEFTPaidSamplingStage.PaidFlagSampleComposition' if '.PaidFlagSampleComposition.' in n else 'LightEFTSpanners.StoredFlagSampleEncoding') for n in interfaces}
        axioms=['Classical.choice','Quot.sound','propext']; names=roots+interfaces+axioms
        inv='owner\tname\tkind\tunsafe\tpartial\n'
        dep='name\towner\tkind\ttypeDependencies\tbodyDependencies\tunsafe\tpartial\n'
        for i,n in enumerate(roots):
            kind='theorem' if i<12 else 'definition';inv+=f'{module}\t{n}\t{kind}\tfalse\tfalse\n'
            dep+=f'{n}\t{module}\t{kind}\t\t'+','.join(interfaces+axioms)+'\tfalse\tfalse\n'
        for n in interfaces:dep+=f'{n}\t{imported[n]}\ttheorem\t\t\tfalse\tfalse\n'
        for n in axioms:dep+=f'{n}\t[anonymous]\taxiom\t\t\tfalse\tfalse\n'
        put(root/'actual-owner-inventory.tsv',inv.encode());put(root/'recursive-dependencies.tsv',dep.encode())
        put(root/'strict-violations.txt',b'\n');put(root/'import-closure-loaded.txt',('\n'.join([*CONTRACT['imports'][module],module])+'\n').encode())
        raw=f'PASS: {len(roots)} new-module actual-owner declarations; {len(names)} recursive constants, 0 opaque bodies; axioms [Classical.choice, Quot.sound, propext]'
        return root,module,{m:{} for m in CONTRACT['imports'][module]},raw

    def test_full_audit_verifier_exact_imports_roots_closure_and_axioms(self):
        for mutation in ['none','imports','unsafe','partial','root','dangling','project-axiom','strict','counts']:
            root,module,deps,raw=self.audit()
            if mutation=='imports':
                p=root/'import-closure-loaded.txt';s=p.read_text();s=s.replace(CONTRACT['imports'][module][0],'OtherProject',1);p.write_text(s)
            elif mutation in ['unsafe','partial']:
                p=root/'recursive-dependencies.tsv';s=p.read_text();s=s.replace('\tfalse\tfalse\n','\ttrue\tfalse\n' if mutation=='unsafe' else '\tfalse\ttrue\n',1);p.write_text(s)
            elif mutation=='root':
                p=root/'actual-owner-inventory.tsv';s=p.read_text().splitlines(True);p.write_text(''.join([s[0],*s[2:]]))
            elif mutation=='dangling':
                p=root/'recursive-dependencies.tsv';p.write_text(p.read_text().replace('Classical.choice,Quot.sound,propext','Missing.Constant',1))
            elif mutation=='project-axiom':
                p=root/'recursive-dependencies.tsv';p.write_text(p.read_text().replace('\ttheorem\t\t\tfalse\tfalse','\taxiom\t\t\tfalse\tfalse',1))
            elif mutation=='strict':(root/'strict-violations.txt').write_text('MODEL violation\n')
            elif mutation=='counts':raw=raw.replace('17 new-module','18 new-module')
            with patch('collision_coverage.validate_collision_coverage',return_value={'MODEL':True}):
                if mutation=='none':self.assertEqual(audit_check.validate(root,deps,raw,module)['new_owner_roots'],17)
                else:
                    with self.assertRaises(RuntimeError):audit_check.validate(root,deps,raw,module)

if __name__=='__main__': unittest.main(verbosity=2)
