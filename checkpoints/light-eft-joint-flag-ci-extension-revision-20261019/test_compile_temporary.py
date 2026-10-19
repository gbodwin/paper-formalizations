"""Real output guard regressions using temporary files; no Lean or child launch.

Authority records and process telemetry are fixtures. Filesystem enumeration,
stat, rename, path/link/size checks and output-guard calls are actual code.
Run with python3 -I -S -B path/to/test_compile_temporary.py.
"""
from pathlib import Path
from contextlib import ExitStack
import copy,io,json,os,stat,sys,tempfile,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
SPEC=json.loads((HERE/'ci-spec.json').read_text())
sys.path[:0]=[str(HERE),str(REPO/SPEC['engine_directory']),str(REPO/'scripts')]
import contracts,output_guards as guard,child_runner,scope
from test_ci_preexec_repair import Fixture as ContextFixture

def put(p,b=b'fixture'):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return p

class Fixture:
 def __init__(self):
  self.storage=tempfile.TemporaryDirectory(prefix='compile-temporary-')
  self.root=Path(self.storage.name);self.objects=self.root/'objects';self.objects.mkdir()
  self.target=self.objects/'LightEFTJointFlagSamplingStage/JointAssignmentLaw.olean';self.target.parent.mkdir()
  self.pid=28019;self.temporary=Path(str(self.target)+'.tmp.'+str(self.pid))
  self.audit=self.root/'audit';self.audit.mkdir()
  self.lock=put(self.root/'fixture.lock');self.fd=os.open(self.lock,os.O_RDONLY);s=os.fstat(self.fd)
  self.record=dict(stage='compile',state='exec-authorized',child_pid=self.pid,supervisor_pid=123,
    child_identity=dict(pid=self.pid,ppid=123,sid=self.pid,pgid=self.pid,start_ticks=456),
    handshake=dict(pid=self.pid,ppid=123,sid=self.pid,pgid=self.pid),kernel_limits_verified=True,
    preexec_binding_verified=True,preexec_verified_ns=100,
    lock=dict(fd=self.fd,path=str(self.lock),device=s.st_dev,inode=s.st_ino),
    output_guard_spec=dict(stage='compile',objects=str(self.objects),target=str(self.target),audit=str(self.audit),protected={}))
 def close(self):os.close(self.fd);self.storage.cleanup()
 def errors(self,**kwargs):return guard.runtime_errors(self.record,**kwargs)

class OutputGuardTests(unittest.TestCase):
 def setUp(self):
  self.stack=ExitStack();self.addCleanup(self.stack.close)
  self.stack.enter_context(patch.object(child_runner.subprocess,'Popen',side_effect=AssertionError('No child launch')))
  self.stack.enter_context(patch.object(child_runner,'run_child',side_effect=AssertionError('No supervisor launch')))
 def fixture(self):
  f=Fixture();self.addCleanup(f.close);return f
 def reject(self,f,path=None,**kwargs):
  errors=f.errors(**kwargs);self.assertTrue(errors)
  self.assertEqual(errors[0],f.record['output_guard_rejection'])
  detail=errors[0];self.assertIn('path',detail);self.assertIn('stat',detail);self.assertIn('stat_error',detail)
  if path is not None:self.assertEqual(detail['path'],str(path))
  return detail
 def test_legitimate_creation_growth_and_atomic_rename(self):
  f=self.fixture();self.assertEqual(f.errors(),[])
  put(f.temporary,b'');self.assertEqual(f.errors(),[])
  f.temporary.write_bytes(b'object bytes');inode=f.temporary.stat().st_ino
  self.assertEqual(f.errors(),[]);f.temporary.rename(f.target)
  self.assertEqual(f.errors(),[]);self.assertEqual(f.target.stat().st_ino,inode)
  self.assertEqual(set(guard.live_objects(f.objects,f.target,True)),{str(f.target)})
  self.assertEqual(set(contracts.object_outputs(f.objects,f.target,True)),{str(f.target)})
 def test_before_exec_completed_and_other_stages_reject(self):
  cases=[('preexec',lambda f:None,dict(preexec=True)),('owned terminal',lambda f:None,dict(terminal=True)),
    ('handshake-wait',lambda f:f.record.update(state='handshake-wait'),{}),
    ('finished',lambda f:f.record.update(state='finished'),{}),('failed',lambda f:f.record.update(state='failed'),{}),
    ('exit0',lambda f:f.record.update(exit=0),{}),('reaped',lambda f:f.record.update(direct_reaped=True),{}),
    ('confirmation',lambda f:f.record.update(terminal_confirmation={'terminal':True}),{})]
  for name,mutate,kwargs in cases:
   with self.subTest(phase=name):
    f=self.fixture();put(f.temporary);mutate(f);self.reject(f,f.temporary,**kwargs)
  for stage in ['resolve','replay','audit']:
   with self.subTest(stage=stage):
    f=self.fixture();put(f.target);put(f.temporary);f.record['stage']=stage;f.record['output_guard_spec']['stage']=stage
    self.reject(f,f.temporary)
 def test_verified_pid_and_handshake_are_required(self):
  changes=[('no kernel verification',lambda r:r.update(kernel_limits_verified=False)),
    ('string kernel verification',lambda r:r.update(kernel_limits_verified='true')),
    ('no input verification',lambda r:r.update(preexec_binding_verified=False)),
    ('no preexec time',lambda r:r.pop('preexec_verified_ns')),
    ('bad stage',lambda r:r.update(stage='resolve')),('bad spec stage',lambda r:r['output_guard_spec'].update(stage='resolve')),
    ('string pid',lambda r:r.update(child_pid='28019')),('bool pid',lambda r:r.update(child_pid=True)),
    ('zero pid',lambda r:r.update(child_pid=0)),('negative pid',lambda r:r.update(child_pid=-1)),
    ('wrong first pid',lambda r:r['child_identity'].update(pid=28020)),
    ('wrong handshake pid',lambda r:r['handshake'].update(pid=28020)),
    ('wrong session',lambda r:r['handshake'].update(sid=28020)),
    ('wrong parent',lambda r:r['child_identity'].update(ppid=124)),
    ('missing incarnation',lambda r:r['child_identity'].pop('start_ticks'))]
  for name,mutate in changes:
   with self.subTest(authority=name):
    f=self.fixture();put(f.temporary);mutate(f.record);self.reject(f,f.temporary)
 def test_wrong_names_pids_and_companion_temporaries_reject(self):
  for suffix in ['.tmp.28020','.tmp.028019','.tmp.28019.extra','.tmp.28019.tmp','.private.tmp.28019','.server.tmp.28019']:
   with self.subTest(suffix=suffix):
    f=self.fixture();p=put(str(f.target)+suffix);self.reject(f,p)
  f=self.fixture();p=put(f.target.parent/'Other.olean.tmp.28019');self.reject(f,p)
 def test_symlink_hardlink_nonregular_and_oversize_reject(self):
  cases=['symlink','broken symlink','hardlink','directory','fifo','oversize']
  for case in cases:
   with self.subTest(kind=case):
    f=self.fixture()
    if case=='symlink':f.temporary.symlink_to(put(f.root/'elsewhere'))
    elif case=='broken symlink':f.temporary.symlink_to(f.root/'absent')
    elif case=='hardlink':os.link(put(f.root/'elsewhere'),f.temporary)
    elif case=='directory':f.temporary.mkdir()
    elif case=='fifo':os.mkfifo(f.temporary)
    else:
     with f.temporary.open('wb') as stream:stream.truncate(16*1024**2+1)
    detail=self.reject(f,f.temporary);self.assertIsNotNone(detail['stat'])
    self.assertEqual(detail['stat']['inode'],f.temporary.lstat().st_ino)
  f=self.fixture()
  with f.temporary.open('wb') as stream:stream.truncate(16*1024**2)
  self.assertEqual(f.errors(),[])
 def test_symlink_ancestor_and_root_reject(self):
  f=self.fixture();put(f.temporary);parent=f.target.parent;other=f.root/'moved';parent.rename(other);parent.symlink_to(other,target_is_directory=True)
  detail=self.reject(f,parent);self.assertTrue(stat.S_ISLNK(detail['stat']['mode']))
  f=self.fixture();f.objects.rename(f.root/'moved');f.objects.symlink_to(f.root/'moved',target_is_directory=True)
  self.reject(f,f.objects)
 def race(self,f,path,action):
  original=Path.lstat;fired=[]
  def lstat(p,*args,**kwargs):
   if p==path and not fired:
    fired.append(True);action()
   return original(p,*args,**kwargs)
  with patch.object(Path,'lstat',lstat):errors=f.errors()
  self.assertTrue(fired);return errors
 def test_enumeration_stat_rename_race_is_allowed_with_inode_evidence(self):
  f=self.fixture();put(f.temporary);inode=f.temporary.stat().st_ino
  self.assertEqual(self.race(f,f.temporary,lambda:f.temporary.rename(f.target)),[])
  event=f.record['output_guard_atomic_renames'][0]
  self.assertEqual(event['temporary'],str(f.temporary));self.assertEqual(event['enumerated_inode'],inode)
  self.assertEqual(event['destination_stat']['inode'],inode);self.assertFalse(f.temporary.exists())
 def test_nonrename_disappearance_and_wrong_destination_reject(self):
  cases=['absent destination','different inode','copied then removed','symlink destination','linked destination','oversize destination']
  for case in cases:
   with self.subTest(race=case):
    f=self.fixture();put(f.temporary)
    def action():
     if case=='absent destination':f.temporary.unlink()
     elif case=='different inode':f.temporary.rename(f.root/'retained');put(f.target)
     elif case=='copied then removed':put(f.target,f.temporary.read_bytes());f.temporary.unlink()
     elif case=='symlink destination':
      f.temporary.unlink();f.target.symlink_to(put(f.root/'elsewhere'))
     elif case=='linked destination':os.link(f.temporary,f.root/'retained');f.temporary.rename(f.target)
     else:
      with f.temporary.open('wb') as stream:stream.truncate(16*1024**2+1)
      f.temporary.rename(f.target)
    self.assertTrue(self.race(f,f.temporary,action));self.assertIn('output_guard_rejection',f.record)
 def test_arbitrary_disappearing_entries_never_ignored(self):
  for name in ['Other.olean','JointAssignmentLaw.olean.tmp.28020','JointAssignmentLaw.olean']:
   with self.subTest(name=name):
    f=self.fixture();p=put(f.target.parent/name)
    self.assertTrue(self.race(f,p,lambda:p.unlink()))
    detail=f.record['output_guard_rejection'];self.assertEqual(detail['path'],str(p));self.assertIsNone(detail['stat'])
    self.assertIn('FileNotFoundError',detail['stat_error'])
 def test_temporary_reappearance_during_confirmation_rejects(self):
  f=self.fixture();put(f.temporary);original=Path.lstat;fired=[]
  def lstat(p,*args,**kwargs):
   if p==f.temporary and not fired:
    fired.append(True);f.temporary.rename(f.target);put(f.temporary)
    raise FileNotFoundError(2,'simulated stat interval',str(p))
   return original(p,*args,**kwargs)
  with patch.object(Path,'lstat',lstat):self.assertTrue(f.errors())
  self.assertIn('reappeared',f.record['output_guard_rejection']['error'])
 def test_stat_permission_errors_are_not_rename_evidence(self):
  f=self.fixture();put(f.temporary);original=Path.lstat
  def lstat(p,*args,**kwargs):
   if p==f.temporary:raise PermissionError(13,'fixture denial',str(p))
   return original(p,*args,**kwargs)
  with patch.object(Path,'lstat',lstat):self.reject(f,f.temporary)
  self.assertIn('PermissionError',f.record['output_guard_rejection']['stat_error'])
 def test_enumeration_error_records_parent_stat(self):
  f=self.fixture()
  with patch.object(guard.os,'scandir',side_effect=PermissionError(13,'fixture enumeration',str(f.objects))):
   detail=self.reject(f,f.objects)
  self.assertEqual(detail['stat']['inode'],f.objects.stat().st_ino)
  self.assertIn('PermissionError',detail['stat_error'])
 def test_missing_error_without_ENOENT_is_rejected(self):
  f=self.fixture();put(f.temporary);original=Path.lstat
  def lstat(p,*args,**kwargs):
   if p==f.temporary:raise FileNotFoundError('unclassified fixture stat failure')
   return original(p,*args,**kwargs)
  with patch.object(Path,'lstat',lstat):self.reject(f,f.temporary)
 def test_leftovers_are_rejected_by_unchanged_completion_contract(self):
  f=self.fixture();put(f.target);put(f.temporary)
  self.assertEqual(f.errors(),[])
  with self.assertRaises(contracts.Rejected):contracts.object_outputs(f.objects,f.target,True)
  with self.assertRaises(contracts.Rejected):guard.live_objects(f.objects,f.target,True)
  self.reject(f,f.temporary,terminal=True)
 def test_real_CI_preexec_rejects_a_temporary(self):
  f=ContextFixture();self.addCleanup(f.close);f.prepare()
  put(str(f.ctx.target)+'.tmp.28019')
  with self.assertRaises((ValueError,RuntimeError)):f.preexec()
 def test_audit_and_protected_inputs_remain_enforced(self):
  f=self.fixture();p=put(f.audit/'actual-owner-inventory.tsv');self.reject(f,p)
  f=self.fixture();protected=put(f.root/'protected');f.record['output_guard_spec']['protected'][str(protected)]=contracts.bind(protected)
  protected.write_bytes(b'changed');self.reject(f,protected)
  f=self.fixture();put(f.target);f.record['stage']='audit';f.record['output_guard_spec']['stage']='audit'
  self.assertEqual(f.errors(),[])
  p=put(f.audit/'unknown');self.reject(f,p)
 def test_real_sampler_retains_rejection_path_and_stat(self):
  f=self.fixture();wrong=put(str(f.target)+'.tmp.28020')
  f.record.update(runtime_wall_started_ns=1,deadline_seconds=90)
  decision=dict(collection_errors=[],accounting={},child={})
  with patch.object(child_runner.exits,'probe',return_value={'terminal':False}),\
       patch.object(child_runner.exits,'assess'),\
       patch.object(child_runner.telemetry,'collect',return_value=decision),\
       patch.object(child_runner.telemetry,'policy_errors',side_effect=lambda s,*a:[repr(e) for e in s['collection_errors']]),\
       patch.object(child_runner,'kill_memory_group') as kill:
   with tempfile.TemporaryFile(mode='w+') as samples:
    with self.assertRaises(child_runner.MemoryGuardError):
     child_runner.runtime_sample(object(),{},None,None,f.record,lambda:None,samples)
    samples.seek(0);persisted=json.loads(samples.read())
   kill.assert_called_once()
  detail=persisted['collection_errors'][0]['error'];self.assertEqual(detail['path'],str(wrong))
  self.assertEqual(detail['stat']['inode'],wrong.lstat().st_ino)
  self.assertEqual(f.record['stop_decision_sample'],persisted)
 def test_real_sampler_passes_owned_terminal_to_guard(self):
  f=self.fixture();put(f.target);put(f.temporary);decision=dict(collection_errors=[],accounting={},child={})
  with patch.object(child_runner.exits,'probe',return_value={'terminal':True}),\
       patch.object(child_runner.exits,'assess'),\
       patch.object(child_runner.telemetry,'collect',return_value=decision),\
       patch.object(child_runner.telemetry,'policy_errors',side_effect=lambda s,*a:[repr(e) for e in s['collection_errors']]),\
       patch.object(child_runner,'kill_memory_group'):
   with tempfile.TemporaryFile(mode='w+') as samples:
    with self.assertRaises(child_runner.MemoryGuardError):
     child_runner.runtime_sample(object(),{},None,None,f.record,lambda:None,samples)
  self.assertTrue(f.record['output_guard_rejection']['terminal'])

if __name__=='__main__':unittest.main(verbosity=2)
