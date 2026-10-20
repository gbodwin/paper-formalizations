"""Admission output-contract models through the real first runtime_sample.

Only collection, exit probes and signal delivery are mocked; the real context
before_child, live guard and memory-policy/sample persistence path execute.
No compiler, process, lock acquisition, real signal/wait or rlimit is permitted.
"""
from pathlib import Path
import contextlib,copy,fcntl,importlib.util,json,os,resource,signal,subprocess,sys,tempfile,time,types,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[1]
sys.dont_write_bytecode=True;sys.path.insert(0,str(HERE));sys.path.insert(0,str(REPO/'scripts'))
import ci_admission,ci_gate,scope,output_guards
from ci_handoff_contract import CONTRACT
from ci_inventory import CIInventory
from contracts import bind,TARGET

def forbid(*a,**k):raise AssertionError('Real process/lease/resource mutation forbidden in admission models')
def put(path,data=b'NONCOMPILER MODEL; NOT A LEAN OBJECT'):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data);return path
def account():
 return dict(namespace='model',membership='model',identities=['model'],headroom=8*1024**3,system_available=8*1024**3,nodes=[dict(path='/model',limit=str(16*1024**3),current=1,memory_stat={'anon':1},oom={'oom':0},pids_max='100',pids_current=1,pids_events={'max':0})])
class AdmissionOutputModels(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  # Authenticate/execute the same source-only supervisor import as the gate.
  # Avoid depending on test discovery order or another adapter's module cache.
  with patch.dict(sys.modules,{'output_guards':output_guards}):
   s=importlib.util.spec_from_file_location('admission_output_model_runner',HERE/'child_runner.py');cls.runner=importlib.util.module_from_spec(s);s.loader.exec_module(cls.runner)
 def fixture(self,module):
  tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);root=Path(tmp.name);objects=root/'work/objects';objects.mkdir(parents=True)
  inputs_root=root/'inputs';inputs_root.mkdir();deps={}
  for m in CONTRACT['replay_order']:
   p=put(inputs_root/Path(*m.split('.')).with_suffix('.olean'));deps[m]=dict(bind(p),module=m,accepted_staged_olean_parts=1)
  source=put(root/'source/Model.lean');inputs={str(source):bind(source)}
  inv=CIInventory([inputs_root],root/'unused-tool',bind);classified=inv.scan();inputs.update(classified['semantic'])
  work=root/'work';evidence=root/'runtime';evidence.mkdir();(evidence/'replay').mkdir()
  lock=put(root/'model-unlocked.lock',b'').open('r+');self.addCleanup(lock.close)
  lease=types.SimpleNamespace(file=lock,acquired_ns=1,path=Path(lock.name),check=lambda:None)
  plan=dict(stage='replay',module=module,argv=['/model/tool/bin/leanchecker','-v',module],env={'LEAN_NUM_THREADS':'1'},sources=[str(source)],source_bindings=[bind(source)],cwd=str(work))
  identity={'GITHUB_SHA':'a'*40}
  base=ci_gate.context_type(scope.Context,work,evidence,[plan],[objects,inputs_root],deps,identity,inputs,inv,classified,bind)
  expected=deps[module]['path'];context=ci_admission.context_type(base,module,expected)(lease);context.target.parent.mkdir(parents=True)
  st=os.fstat(lock.fileno());record=dict(stage='replay',argv=plan['argv'],environment=plan['env'],state='created',supervisor_pid=os.getpid(),deadline_seconds=90,lock=dict(fd=lock.fileno(),path=lock.name,device=st.st_dev,inode=st.st_ino))
  context.before_child(plan,record,lambda:None)
  with patch.dict(sys.modules,{'child_runner':self.runner}),patch.object(self.runner,'assert_idle'),patch.object(ci_gate.shutil,'disk_usage',return_value=types.SimpleNamespace(free=3*1024**3)):
   context.prepare_child(plan,record,lambda:None,types.SimpleNamespace(sample=account))
  record.update(state='handshake-wait',child_pid=12345,runtime_wall_started_ns=time.monotonic_ns())
  return types.SimpleNamespace(root=root,context=context,record=record,expected=Path(expected),plan=plan)
 def first_sample(self,f,should_fail=False):
  runner=self.runner;baseline=account();now=time.monotonic_ns()
  decision=dict(sample_utc='MODEL',sample_started_ns=now,sample_finished_ns=now+1,accounting=copy.deepcopy(baseline),child=dict(pid=12345,start_ticks=1,state='S',rss=1,vm=1,collection_errors=[]),collection_errors=[])
  def assess(child,sample,record,before,descendants):
   sample['exit_lifecycle']={'terminal_confirmed':False};sample['observed_process_memory']=dict(rss=1,vm=1)
  with patch.object(runner.exits,'probe',return_value={'terminal':False}),patch.object(runner.exits,'assess',side_effect=assess),patch.object(runner.telemetry,'collect',return_value=decision),patch.object(runner,'kill_memory_group') as kill,patch.object(runner,'audit_output_errors',wraps=output_guards.runtime_errors) as real_guard:
   path=f.root/('sample-'+str(len(list(f.root.glob('sample-*'))))+'.jsonl')
   with path.open('x') as samples:
    if should_fail:
     with self.assertRaises(runner.MemoryGuardError):runner.runtime_sample(types.SimpleNamespace(pid=12345),baseline,None,None,f.record,lambda:None,samples)
     kill.assert_called_once()
    else:
     runner.runtime_sample(types.SimpleNamespace(pid=12345),baseline,None,None,f.record,lambda:None,samples);kill.assert_not_called()
   real_guard.assert_called_once_with(f.record,preexec=False,terminal=False)
  self.assertEqual(f.record['state'],'handshake-wait');self.assertNotIn('handshake',f.record);self.assertNotIn('preexec_verified_ns',f.record)
  self.assertEqual(bool(decision['collection_errors']),should_fail)
  return decision
 def test_actual_first_handshake_wait_sample_accepts_all_three_admissions(self):
  for module in CONTRACT['replay_order']:
   with self.subTest(module=module):
    f=self.fixture(module);self.assertFalse(f.context.target.exists());self.assertEqual(f.record['output_guard_spec']['admission_only'],dict(module=module,object=str(f.expected)))
    self.assertIn(str(f.expected),f.record['output_guard_spec']['protected']);self.first_sample(f)
    self.assertEqual(list(f.context.objects.rglob('*.olean')),[])
 def test_same_contract_applies_preexec_live_and_terminal(self):
  for module in CONTRACT['replay_order']:
   f=self.fixture(module)
   for preexec,terminal in [(False,False),(True,False),(False,True)]:
    with self.subTest(module=module,preexec=preexec,terminal=terminal):self.assertEqual(output_guards.runtime_errors(f.record,preexec,terminal),[])
 def test_forbidden_generated_files_sidecars_temporaries_and_directories_fail_first_sample(self):
  for module in CONTRACT['replay_order']:
   for kind in ['target','.olean.server','.olean.private','.ilean','.ir','.ir.sig','compile-temporary','unrelated-file','unplanned-directory','audit-export']:
    with self.subTest(module=module,kind=kind):
     f=self.fixture(module);target=f.context.target
     if kind=='target':put(target)
     elif kind.startswith('.'):put(str(target)[:-len('.olean')]+kind)
     elif kind=='compile-temporary':put(str(target)+'.tmp.12345')
     elif kind=='unrelated-file':put(f.context.objects/'Other.olean')
     elif kind=='unplanned-directory':(f.context.objects/'Other').mkdir()
     else:put(f.context.audit/'actual-owner-inventory.tsv')
     self.first_sample(f,True)
 def test_symlink_hardlink_and_nonregular_output_fail(self):
  for kind in ['symlink','hardlink','fifo']:
   f=self.fixture(CONTRACT['replay_order'][0]);target=f.context.target
   if kind=='symlink':target.symlink_to(f.expected)
   elif kind=='hardlink':os.link(put(f.root/'unprotected-model'),target)
   else:os.mkfifo(target)
   self.first_sample(f,True)
 def test_selected_existing_input_mutation_fails_real_first_sample(self):
  for module in CONTRACT['replay_order']:
   f=self.fixture(module);f.expected.write_bytes(b'changed admitted object');self.first_sample(f,True)
 def test_malformed_or_misapplied_admission_contract_never_weakens_ordinary_replay(self):
  mutations=[lambda r:r['output_guard_spec'].update(admission_only=False),lambda r:r['output_guard_spec']['admission_only'].update(module=TARGET),lambda r:r.update(context_admission_module=TARGET),lambda r:r.update(argv=['/model/leanchecker','-v',TARGET]),lambda r:r.update(stage='compile'),lambda r:r['output_guard_spec'].update(stage='compile'),lambda r:r.update(context_qualification='wrong'),lambda r:r['output_guard_spec']['protected'].pop(r['output_guard_spec']['admission_only']['object']),lambda r:r['context_admission_selection'].update(prefix_matches=[])]
  for mutate in mutations:
   f=self.fixture(CONTRACT['replay_order'][0]);mutate(f.record)
   self.assertTrue(output_guards.runtime_errors(f.record))
 def test_ordinary_missing_target_still_rejected_at_first_handshake_sample(self):
  f=self.fixture(CONTRACT['replay_order'][0]);f.record['output_guard_spec'].pop('admission_only');f.record['argv']=['/model/leanchecker','-v',TARGET]
  self.first_sample(f,True);self.assertIn('Missing completed target',f.record['output_guard_rejection']['error'])
 def test_ordinary_completed_target_accepted_and_compile_empty_behavior_unchanged(self):
  for stage in ['compile','resolve','replay','audit']:
   f=self.fixture(CONTRACT['replay_order'][0]);f.record['output_guard_spec'].pop('admission_only');f.record['stage']=stage;f.record['output_guard_spec']['stage']=stage
   if stage!='compile':put(f.context.target)
   self.assertEqual(output_guards.runtime_errors(f.record),[])
 def resolution_output(self,f,kind):
  path=f.context.work/'resolution.json'
  if kind=='regular':put(path,b'UNAUTHORIZED MODEL RESOLUTION')
  else:
   path.symlink_to(f.context.work/'missing-resolution-target')
   self.assertFalse(path.exists());self.assertTrue(path.is_symlink())
  self.assertEqual(f.context.resolved,{})
  return path
 def test_resolution_file_and_dangling_symlink_fail_actual_first_sample(self):
  for module in CONTRACT['replay_order']:
   for kind in ['regular','dangling-symlink']:
    with self.subTest(module=module,kind=kind):
     f=self.fixture(module);path=self.resolution_output(f,kind);self.first_sample(f,True)
     rejection=f.record['output_guard_rejection']
     self.assertEqual(rejection['path'],str(path));self.assertIsNotNone(rejection['stat'])
     self.assertIn('Admission resolution output appeared',rejection['error'])
 def test_resolution_file_and_dangling_symlink_fail_actual_after_child(self):
  for module in CONTRACT['replay_order']:
   for kind in ['regular','dangling-symlink']:
    with self.subTest(module=module,kind=kind):
     f=self.fixture(module);self.first_sample(f)
     put(f.context.stage_evidence/'raw.log',('replaying '+module+'\n').encode())
     f.record.update(state='finished',exit=0)
     path=self.resolution_output(f,kind)
     with self.assertRaises(output_guards.LiveOutputRejected) as rejected:
      f.context.after_child(f.plan,f.record,lambda:None)
     self.assertEqual(rejected.exception.observation['path'],str(path))
     self.assertEqual(f.context.seen,[]);self.assertIs(f.record['between_child_preservation_passed'],False)
 def test_absent_resolution_passes_actual_after_child_for_all_three_admissions(self):
  for module in CONTRACT['replay_order']:
   with self.subTest(module=module):
    f=self.fixture(module);self.first_sample(f)
    put(f.context.stage_evidence/'raw.log',('replaying '+module+'\n').encode())
    f.record.update(state='finished',exit=0)
    f.context.after_child(f.plan,f.record,lambda:None)
    self.assertEqual(f.context.seen,[f.plan]);self.assertTrue(f.record['between_child_preservation_passed'])
    self.assertEqual(f.context.resolved,{})
 def test_context_full_verification_rejects_persistent_generated_output(self):
  for module in CONTRACT['replay_order']:
   f=self.fixture(module);put(f.context.objects/'Other.olean')
   with self.assertRaises(RuntimeError):f.context.verify(False)

if __name__=='__main__':
 with contextlib.ExitStack() as stack:
  for obj,names in [(subprocess,['Popen','run','check_output']),(os,['fork','execve','kill','killpg','waitpid','waitid']),(resource,['setrlimit','prlimit']),(fcntl,['flock']),(signal,['setitimer'])]:
   for name in names:stack.enter_context(patch.object(obj,name,forbid))
  unittest.main(verbosity=2)
