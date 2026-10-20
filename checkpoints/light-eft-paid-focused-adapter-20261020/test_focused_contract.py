"""Actual context/first runtime sample with filesystem models; no Lean or child."""
from pathlib import Path
import ast,contextlib,copy,fcntl,hashlib,importlib.util,json,os,resource,signal,subprocess,sys,tempfile,time,types,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];BASE=ROOT/'checkpoints/light-eft-canonical-output-adapter-20261020'
sys.dont_write_bytecode=True;sys.path.insert(0,str(BASE));sys.path.insert(0,str(HERE));sys.path.insert(0,str(ROOT/'scripts'))
import ci_gate,output_guards,audit_check
from focused_context import FocusedContext
from finite_contract import CONTRACT
from contracts import bind
from ci_inventory import CIInventory
def forbidden(*a,**k):raise AssertionError('Process/lease/resource operation forbidden in source models')
def put(p,data=b'FILESYSTEM MODEL; NOT A LEAN OBJECT'):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return p
def account():return dict(namespace='model',membership='model',identities=['model'],headroom=8*1024**3,system_available=8*1024**3,nodes=[dict(path='/model',limit=str(16*1024**3),current=1,memory_stat={'anon':1},oom={'oom':0},pids_max='100',pids_current=1,pids_events={'max':0})])
class FocusedModels(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  spec=importlib.util.spec_from_file_location('child_runner',BASE/'child_runner.py');cls.runner=importlib.util.module_from_spec(spec);sys.modules['child_runner']=cls.runner;spec.loader.exec_module(cls.runner)
 def fixture(self,index=4):
  tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);root=Path(tmp.name);work=root/'work';objects=work/'objects';(objects/'LightEFTPaidSamplingStage').mkdir(parents=True);(work/'resolution').mkdir();evidence=root/'runtime';evidence.mkdir()
  inputroot=root/'inputs';inputroot.mkdir();deps={}
  spec=json.loads((HERE/'ci-spec.json').read_text())
  for row in spec['dependencies']:
   m=row['module'];p=put(inputroot/Path(*m.split('.')).with_suffix('.olean'));deps[m]=dict(bind(p),module=m)
  roots=[objects,inputroot];plans=ci_gate.build_plans(root/'tool',work,spec,roots,'a'*40,bind)
  inv=CIInventory([inputroot],root/'tool',bind);classified=inv.scan();inputs=dict(classified['semantic'])
  for p in plans:
   for s in p['sources']:inputs[s]=bind(s)
  lock=put(root/'unlocked-model.lock',b'').open('r+');self.addCleanup(lock.close)
  lease=types.SimpleNamespace(file=lock,path=Path(lock.name),acquired_ns=1,check=lambda:None)
  ctx=FocusedContext(lease,work,evidence,plans,roots,deps,{'GITHUB_SHA':'a'*40},inputs,inv,classified)
  # Model a completed prior module with real immutable file bindings. This is
  # not a simulated successful Lean receipt or an acceptance claim.
  for m in CONTRACT['modules'][:(2 if index==8 else 1 if index>=4 else 0)]:
   p=put(ctx.target(m));ctx.new[str(p)]=bind(p)
  if index>=4:
   path=put(work/'resolution/PaidFlagSerialization.json',b'MODEL COMPLETED RESOLUTION');ctx.resolved[str(path)]=bind(path)
   for name in ['actual-owner-inventory.tsv','recursive-dependencies.tsv','import-closure-loaded.txt','strict-violations.txt']:
    path=put(work/'audit/PaidFlagSerialization/ci-evidence'/name,b'MODEL COMPLETED AUDIT');ctx.audit_files[str(path)]=bind(path)
  ctx.seen=plans[:index];p=plans[index];folder=evidence/p['case']/p['stage'];folder.mkdir()
  st=os.fstat(lock.fileno());record=dict(stage=p['stage'],argv=p['argv'],environment=p['env'],state='created',supervisor_pid=os.getpid(),deadline_seconds=90,lock=dict(fd=lock.fileno(),path=lock.name,device=st.st_dev,inode=st.st_ino))
  ctx.before_child(p,record,lambda:None)
  with patch.object(self.runner,'assert_idle'),patch('focused_context.shutil.disk_usage',return_value=types.SimpleNamespace(free=3*1024**3)):
   ctx.prepare_child(p,record,lambda:None,types.SimpleNamespace(sample=account))
  record.update(state='handshake-wait',child_pid=12345,runtime_wall_started_ns=time.monotonic_ns())
  return types.SimpleNamespace(root=root,ctx=ctx,record=record,plan=p,plans=plans)
 def first_sample(self,f,fail=False):
  now=time.monotonic_ns();sample=dict(sample_utc='MODEL',sample_started_ns=now,sample_finished_ns=now+1,accounting=account(),child=dict(pid=12345,start_ticks=1,state='S',rss=1,vm=1,collection_errors=[]),collection_errors=[])
  def assess(child,s,r,before,desc):s.update(exit_lifecycle={'terminal_confirmed':False},observed_process_memory=dict(rss=1,vm=1))
  runner=self.runner
  with patch.object(runner.exits,'probe',return_value={'terminal':False}),patch.object(runner.exits,'assess',side_effect=assess),patch.object(runner.telemetry,'collect',return_value=sample),patch.object(runner,'kill_memory_group') as kill,patch.object(runner,'audit_output_errors',wraps=output_guards.runtime_errors) as guard:
   with (f.root/'sample.jsonl').open('x') as log:
    if fail:
     with self.assertRaises(runner.MemoryGuardError):runner.runtime_sample(types.SimpleNamespace(pid=12345),account(),None,None,f.record,lambda:None,log)
     kill.assert_called_once()
    else:runner.runtime_sample(types.SimpleNamespace(pid=12345),account(),None,None,f.record,lambda:None,log);kill.assert_not_called()
   guard.assert_called_once_with(f.record,preexec=False,terminal=False)
  self.assertNotIn('handshake',f.record);self.assertNotIn('preexec_verified_ns',f.record)
 def test_first_handshake_sample_accepts_empty_A_compile_and_B_with_preserved_A(self):
  for index in [0,4,8]:
   f=self.fixture(index);self.first_sample(f)
   if index==4:self.assertIn(str(f.ctx.target(CONTRACT['modules'][0])),f.record['output_guard_spec']['protected'])
 def test_preserved_A_mutation_removal_link_and_foreign_output_fail_actual_first_sample(self):
  for kind in ['mutation','removal','symlink','hardlink','foreign','temporary','unexpected-directory']:
   with self.subTest(kind=kind):
    f=self.fixture();a=f.ctx.target(CONTRACT['modules'][0]);b=f.ctx.target(CONTRACT['modules'][1])
    if kind=='mutation':a.write_bytes(b'changed')
    elif kind=='removal':a.unlink()
    elif kind=='symlink':a.unlink();a.symlink_to(put(f.root/'outside'))
    elif kind=='hardlink':a.unlink();os.link(put(f.root/'outside'),a)
    elif kind=='foreign':put(f.ctx.objects/'LightEFTPaidSamplingStage/Other.olean')
    elif kind=='temporary':put(str(b)+'.tmp.12345')
    else:(f.ctx.objects/'Other').mkdir()
    self.first_sample(f,True)
 def test_resolution_regular_and_dangling_or_audit_outside_phase_fail_first_sample(self):
  for kind in ['regular','dangling','audit']:
   f=self.fixture();p=f.ctx.work/'resolution/PaidFlagSampleComposition.json'
   if kind=='regular':put(p)
   elif kind=='dangling':p.symlink_to(f.ctx.work/'absent')
   else:put(f.ctx.work/'audit/PaidFlagSampleComposition/ci-evidence/strict-violations.txt')
   self.first_sample(f,True)
 def test_B_emitted_parts_allowed_and_A_stays_identical(self):
  f=self.fixture();a=f.ctx.target(CONTRACT['modules'][0]);before=bind(a)
  put(f.ctx.target(CONTRACT['modules'][1]));self.first_sample(f);self.assertEqual(bind(a),before)
 def test_fresh_second_target_required_without_emptying_shared_first_package(self):
  f=self.fixture();a=f.ctx.target(CONTRACT['modules'][0]);before=bind(a);put(f.ctx.target(CONTRACT['modules'][1]))
  with self.assertRaisesRegex(RuntimeError,'not absent before compile'):f.ctx.before_child(f.plan,{},lambda:None)
  self.assertEqual(bind(a),before)
 def test_completed_resolution_and_audit_mutations_fail_actual_first_sample(self):
  for kind in ['resolution','audit']:
   f=self.fixture();path=next(iter(f.ctx.resolved if kind=='resolution' else f.ctx.audit_files));Path(path).write_bytes(b'changed')
   self.first_sample(f,True)
 def test_postchild_full_verification_refuses_changed_first_object(self):
  f=self.fixture();put(f.ctx.target(CONTRACT['modules'][1]));f.ctx.target(CONTRACT['modules'][0]).write_bytes(b'changed')
  f.record['exit']=0
  with self.assertRaises(RuntimeError):f.ctx.after_child(f.plan,f.record,lambda:None)
 def test_real_preexec_accepts_unchanged_and_rejects_mutated_prior_object(self):
  for mutate in [False,True]:
   f=self.fixture()
   if mutate:f.ctx.target(CONTRACT['modules'][0]).write_bytes(b'changed')
   with patch('focused_context.shutil.disk_usage',return_value=types.SimpleNamespace(free=3*1024**3)):
    if mutate:
     with self.assertRaises(ValueError):f.ctx.preexec(f.plan,f.record,lambda:None)
    else:
     f.ctx.preexec(f.plan,f.record,lambda:None);self.assertTrue(f.record['preexec_binding_verified'])
 def test_real_postcompile_freezes_B_then_real_resolve_first_sample_preserves_A(self):
  f=self.fixture();a=f.ctx.target(CONTRACT['modules'][0]);before=bind(a);b=put(f.ctx.target(CONTRACT['modules'][1]))
  put(f.ctx.evidence/f.plan['case']/'compile/raw.log',b'');f.record['exit']=0
  f.ctx.after_child(f.plan,f.record,lambda:None);self.assertEqual(bind(a),before);self.assertIn(str(b),f.ctx.new)
  p=f.plans[5];(f.ctx.evidence/p['case']/'resolve').mkdir();r=dict(stage=p['stage'],argv=p['argv'],environment=p['env'],state='created',supervisor_pid=os.getpid(),deadline_seconds=90,lock=f.record['lock'])
  f.ctx.before_child(p,r,lambda:None)
  with patch.object(self.runner,'assert_idle'),patch('focused_context.shutil.disk_usage',return_value=types.SimpleNamespace(free=3*1024**3)):
   f.ctx.prepare_child(p,r,lambda:None,types.SimpleNamespace(sample=account))
  r.update(state='handshake-wait',child_pid=12345,runtime_wall_started_ns=time.monotonic_ns());f.plan=p;f.record=r
  self.assertEqual(len(r['effective_dependencies']),17);self.first_sample(f);self.assertEqual(bind(a),before)
 def test_fixture_mode_preserves_both_and_forbids_any_new_object(self):
  f=self.fixture(8);put(f.ctx.objects/'LightEFTPaidSamplingStage/PaidFlagFixtures.olean');self.first_sample(f,True)
 def test_missing_or_forged_completed_ledger_or_split_root_rejected(self):
  for mutate in [lambda s:s['focused'].update(completed=[]),lambda s:s['focused'].update(completed_modules=[]),lambda s:s.update(objects='/different/objects'),lambda s:s.update(admission_only={})]:
   f=self.fixture();mutate(f.record['output_guard_spec']);self.first_sample(f,True)
 def test_stage_B_resolve_replay_audit_all_preserve_A(self):
  for index in [5,6,7]:
   f=self.fixture(index=4);put(f.ctx.target(CONTRACT['modules'][1]));f.ctx.new[str(f.ctx.target(CONTRACT['modules'][1]))]=bind(f.ctx.target(CONTRACT['modules'][1]))
   p=f.plans[index];f.record.update(stage=p['stage'],argv=p['argv'],working_directory=p['cwd'],output_guard_spec=f.ctx.spec(p))
   self.assertEqual(output_guards.runtime_errors(f.record),[])
 def test_per_module_import_sets_from_actual_source_graph(self):
  spec=json.loads((HERE/'ci-spec.json').read_text());paths={x['module']:ROOT/x['path'] for x in spec['dependencies']}
  paths.update({m:ROOT/next(x['path'] for x in spec['sources'] if x['role']==role) for m,role in zip(CONTRACT['modules'],['serialization','composition'])})
  import re
  def visit(m,seen):
   for n in re.findall(r'^import\s+(\S+)',paths[m].read_text(),re.M):
    if n in paths and n not in seen:seen.add(n);visit(n,seen)
  for m,count in zip(CONTRACT['modules'],[13,17]):
   seen=set();visit(m,seen);self.assertEqual(seen,set(CONTRACT['imports'][m]));self.assertEqual(len(seen),count)
  with tempfile.TemporaryDirectory() as folder:
   for n in ['actual-owner-inventory.tsv','recursive-dependencies.tsv','import-closure-loaded.txt','strict-violations.txt']:put(Path(folder)/n,b'\n')
   same_count_A=set(CONTRACT['imports'][CONTRACT['modules'][0]]);same_count_A.remove('LightEFTSpanners.ControllerTrace');same_count_A.add('LightEFTSpanners.StoredFlagSample')
   same_count_B=set(CONTRACT['imports'][CONTRACT['modules'][1]]);same_count_B.remove(CONTRACT['modules'][0]);same_count_B.add('LightEFTSpanners.StoredCanonicalAssignmentOutput')
   for m,bad in [(CONTRACT['modules'][0],{x['module']:{} for x in spec['dependencies']}),(CONTRACT['modules'][1],{x:{} for x in CONTRACT['imports'][CONTRACT['modules'][1]] if x!=CONTRACT['modules'][0]}),(CONTRACT['modules'][0],{x:{} for x in same_count_A}),(CONTRACT['modules'][1],{x:{} for x in same_count_B})]:
    with self.assertRaisesRegex(RuntimeError,'per-module dependency'):audit_check.validate(folder,bad,'MODEL\n',m)
 def test_finite_order_stops_at_every_first_failure_and_rejects_bad_schedule(self):
  f=self.fixture();plans=f.plans
  for failure in range(9):
   events=[]
   def child(p):
    i=len(events);events.append(p)
    if i==failure:raise RuntimeError('model first failure')
    return {'attempt_id':str(i)}
   with self.assertRaises(RuntimeError):ci_gate.execute_sequence(plans,child,lambda:None)
   self.assertEqual(len(events),failure+1)
  for bad in [plans[:-1],plans+plans[:1],list(reversed(plans))]:
   with self.assertRaises(ValueError):ci_gate.execute_sequence(bad,lambda p:self.fail('child launched'),lambda:None)
 def test_compiler_launcher_config_and_flags_keep_accepted_bounds(self):
  f=self.fixture()
  for p in f.plans:
   self.assertLessEqual(len(json.dumps({k:p[k] for k in ['argv','env','stage']}).encode()),4096)
   self.assertEqual(p['env']['LEAN_NUM_THREADS'],'1')
   if p['stage']!='replay':self.assertEqual(p['argv'][1:6],ci_gate.FLAGS)
  spec=json.loads((HERE/'ci-spec.json').read_text());tool=Path('/home/runner/.elan/toolchains/leanprover--lean4---v4.34.0')
  checkout=Path('/home/runner/work/paper-formalizations/paper-formalizations');work=Path('/home/runner/work/_temp/light-eft-paid-focused-99999999999-1/work')
  roots=[work/'objects',checkout/'.lake/build/lib/lean',*[checkout/'.lake/packages'/name/'.lake/build/lib/lean' for name in spec['pins']],tool/'lib/lean']
  for p in ci_gate.build_plans(tool,work,spec,roots,'a'*40,bind):self.assertLessEqual(len(json.dumps({k:p[k] for k in ['argv','env','stage']}).encode()),4096)
 def test_audit_collision_engine_and_recursive_walk_are_retained(self):
  baseline=(BASE/'staged/CanonicalOutputAudit.lean').read_text();core=baseline[baseline.index('/- Verification helper'):baseline.index('/- Unexecuted focused audit draft')]
  for name in ['SerializationAudit.lean','CompositionAudit.lean']:
   s=(HERE/'staged'/name).read_text();self.assertIn(core,s)
  for text in ['opaqueInfo v => v.value.getUsedConstants','inductInfo v => (v.all ++ v.ctors).toArray','ctorInfo v => #[v.induct]','recInfo v => v.rules.foldl']:
   self.assertIn(text,(HERE/'staged/SerializationAudit.lean').read_text())

if __name__=='__main__':
 with contextlib.ExitStack() as stack:
  for obj,names in [(subprocess,['Popen','run','check_output','call','check_call']),(os,['fork','execve','execv','kill','killpg','waitpid','waitid','system','posix_spawn','posix_spawnp']),(resource,['setrlimit','prlimit']),(fcntl,['flock','lockf']),(signal,['setitimer'])]:
   for name in names:
    if hasattr(obj,name):stack.enter_context(patch.object(obj,name,forbidden))
  unittest.main(verbosity=2)
