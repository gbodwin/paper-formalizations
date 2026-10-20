"""Noncompiler models of audit-only CPU90 and mandatory CPU60 stage reset.

No child, lock, signal, wait or actual resource-limit operation is permitted.
"""
from pathlib import Path
import contextlib,copy,fcntl,importlib.util,json,os,resource,signal,subprocess,sys,tempfile,types,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[1]
OLD=REPO/'checkpoints/light-eft-joint-flag-assignment-corrected-adapter-20261018'
EXT=REPO/'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'
CPU={'compile':60,'resolve':60,'replay':60,'audit':90}
def forbidden(*a,**k):raise AssertionError('Real process/lease/resource mutation forbidden in CPU models')
def expected(stage):return dict(RLIMIT_AS=12*1024**3,RLIMIT_CPU=CPU[stage],RLIMIT_FSIZE=(64 if stage=='audit' else 16)*1024**2,RLIMIT_CORE=0)
def load(name,path,pilot=None):
 original=list(sys.path);sys.path[:0]=[str(path.parent),str(OLD),str(HERE),str(REPO/'scripts')]
 try:
  with patch.dict(sys.modules,{'pilot_child':pilot} if pilot else {}):
   spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
 finally:sys.path[:]=original
class BeforeEvidence(Exception):pass
class NoEvidence:
 def mkdir(self,**kwargs):raise BeforeEvidence('Stop before evidence/process/lease operations')
def prime(runner,stage):
 shared=types.SimpleNamespace(source_commit='a'*40,wrapper_commit='a'*40,fixture=False,visible_gate=lambda p:(4 if p['stage'] in ['replay','audit'] else 3)*1024**3)
 try:runner.run_child(dict(stage=stage,argv=['model'],env={}),Path('/model'),NoEvidence(),shared)
 except BeforeEvidence:return
 raise AssertionError('Model must stop before evidence creation')
def put(path,data):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data);return path
def save(path,data):return put(path,(json.dumps(data)+'\n').encode())

class AuditCPUModels(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.adapters=[]
  for label,directory in [('decoder',OLD),('corollary',HERE)]:
   pilot=load(label+'_cpu_pilot',directory/'pilot_child.py');runner=load(label+'_cpu_runner',directory/'child_runner.py',pilot)
   cls.adapters.append((label,pilot,runner))
  cls.verifiers=[('decoder-scope',load('decoder_cpu_scope',OLD/'scope.py'),'verify_receipts',cls.adapters[0][2],4),
   ('decoder-CI',load('decoder_cpu_receipts',EXT/'ci_receipts.py'),'verify_receipts',cls.adapters[0][2],4),
   ('corollary-CI',load('corollary_cpu_receipts',HERE/'ci_receipts.py'),'verify_receipts',cls.adapters[1][2],4),
   ('corollary-singleton',load('corollary_cpu_singleton',HERE/'ci_admission_receipts.py'),'verify_singleton_receipt',cls.adapters[1][2],1)]
 def setUp(self):
  for _,pilot,runner in self.adapters:
   snapshot=dict(pilot.LIMITS)
   self.addCleanup(lambda p=pilot,s=snapshot:(p.LIMITS.clear(),p.LIMITS.update(s)))
 def test_launcher_audit_to_replay_and_other_stage_reset(self):
  for label,pilot,_ in self.adapters:
   state={}
   def setlimit(key,value):state[key]=value
   with patch.object(resource,'setrlimit',side_effect=setlimit) as calls,patch.object(resource,'getrlimit',side_effect=lambda key:state[key]):
    for stage in ['audit','replay','audit','compile','audit','resolve','audit','replay']:
     with self.subTest(adapter=label,stage=stage):
      result=pilot.configure(stage);self.assertEqual(result,{k:[v,v] for k,v in expected(stage).items()});self.assertEqual(pilot.LIMITS,expected(stage))
    self.assertEqual(calls.call_count,8*4)
 def test_launcher_rejects_incorrect_soft_or_hard_CPU_readback(self):
  for label,pilot,_ in self.adapters:
   for stage,wrong in [('audit',(60,60)),('audit',(89,90)),('audit',(90,91)),('replay',(90,90)),('compile',(90,90)),('resolve',(59,60))]:
    exp=expected(stage)
    with self.subTest(adapter=label,stage=stage,wrong=wrong),patch.object(resource,'setrlimit'),patch.object(resource,'getrlimit',side_effect=lambda key,e=exp,w=wrong:w if key==resource.RLIMIT_CPU else next((v,v) for k,v in e.items() if getattr(resource,k)==key)),self.assertRaisesRegex(RuntimeError,'readback failed: RLIMIT_CPU'):pilot.configure(stage)
 def test_parent_selects_CPU_and_file_limits_before_evidence_with_audit_reset(self):
  for label,_,runner in self.adapters:
   for stage in ['audit','replay','compile','audit','resolve','replay']:
    with self.subTest(adapter=label,stage=stage):prime(runner,stage);self.assertEqual(runner.LIMITS,expected(stage))
 def handshake(self,runner,stage,packet_cpu=None,kernel_cpu=None):
  prime(runner,stage);limits=expected(stage);child=types.SimpleNamespace(pid=1234);identity=dict(start_ticks='model',ppid=111,sid=1234,pgid=1234)
  packet=dict(limits={k:[v,v] for k,v in limits.items()},pid=1234,ppid=111,sid=1234,pgid=1234,lock_fd=7,lock_device=1,lock_inode=2,lock_inheritable=True)
  if packet_cpu is not None:packet['limits']['RLIMIT_CPU']=packet_cpu
  def kernel(pid,key):
   self.assertEqual(pid,1234)
   if key==resource.RLIMIT_CPU and kernel_cpu is not None:return kernel_cpu
   return next((v,v) for k,v in limits.items() if getattr(resource,k)==key)
  st=types.SimpleNamespace(st_dev=1,st_ino=2)
  with patch.object(os,'fstat',return_value=st),patch.object(os,'stat',return_value=st),patch.object(os,'getpid',return_value=111),patch.object(resource,'prlimit',side_effect=kernel):runner.verify_ready(packet,child,7,identity,identity)
 def test_handshake_accepts_exact_audit90_then_replay60(self):
  for label,_,runner in self.adapters:
   for stage in ['audit','replay','compile','resolve']:
    with self.subTest(adapter=label,stage=stage):self.handshake(runner,stage)
 def test_handshake_rejects_wrong_CPU_packet_and_kernel_limits(self):
  for label,_,runner in self.adapters:
   for stage,wrong in [('audit',[60,60]),('audit',[89,90]),('replay',[90,90]),('compile',[90,90]),('resolve',[90,90])]:
    with self.subTest(adapter=label,stage=stage,where='packet'),self.assertRaisesRegex(RuntimeError,'Child limit readback mismatch'):self.handshake(runner,stage,packet_cpu=wrong)
    with self.subTest(adapter=label,stage=stage,where='kernel'),self.assertRaisesRegex(RuntimeError,'Kernel limit readback mismatch'):self.handshake(runner,stage,kernel_cpu=tuple(wrong))
 def fixture(self,module,count):
  bind=module.bind
  tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);root=Path(tmp.name);source=put(root/'Model.lean',b'NONCOMPILER RECEIPT MODEL')
  journal=put(root/'inputs.jsonl',(json.dumps(bind(source))+'\n').encode());iref=bind(journal);plans=[];records=[]
  stages=['compile','resolve','replay','audit'] if count==4 else ['replay']
  src=getattr(module,'APPROVED','a'*40);account=dict(namespace='model',membership='model',identities=['model'],headroom=8*1024**3,system_available=8*1024**3,nodes=[dict(path='/model',limit=str(16*1024**3),current=1,memory_stat={'anon':1},oom={'oom':0},pids_max='100',pids_current=1,pids_events={'max':0})])
  for i,stage in enumerate(stages):
   folder=root/stage;folder.mkdir();binding=bind(source);snapshot=binding['sha256']+'.source';put(folder/snapshot,source.read_bytes())
   plan=dict(stage=stage,argv=['NONCOMPILER',stage],env={'MODEL':'1'},cwd=str(root),sources=[str(source)],source_bindings=[binding]);plans.append(plan)
   start=1000+i*1000;who=dict(pid=200+i,ppid=100,sid=200+i,pgid=200+i,start_ticks='model',rss=1)
   sample=dict(sample_started_ns=start+30,sample_finished_ns=start+40,child=who,accounting=account,collection_errors=[],exit_lifecycle={'terminal_confirmed':True})
   samples=put(folder/'samples.jsonl',(json.dumps(sample)+'\n').encode());raw=put(folder/'raw.log',b'NONCOMPILER MODEL\n')
   r=dict(stage=stage,argv=plan['argv'],environment=plan['env'],working_directory=plan['cwd'],planned_source_bindings=[binding],attempt_id='model-'+str(i),source_commit=src,wrapper_commit='a'*40,frozen_import_source=module.FROZEN,input_inventory_ref=iref,state='finished',exit=0,preexec_binding_verified=True,between_child_preservation_passed=True,waitid_wait4_status_match=True,preexec_binding_strategy='exact identity/membership plus critical hashes',preexec_identity_files=1,preexec_critical_hashes=1,runtime_wall_started_ns=start+1,preexec_validation_started_ns=start+10,preexec_validation_finished_ns=start+11,preexec_verified_ns=start+20,direct_reaped=True,kernel_no_children_verified=True,all_descendants_gone=True,lock={'device':1,'inode':2},started_ns=start,ended_ns=start+100,submitted_sources=[dict(binding,snapshot=snapshot)],kernel_limits_verified=True,handshake={'limits':{k:[v,v] for k,v in expected(stage).items()}},disk_admission_bytes=3*1024**3,preexec_disk_bytes=3*1024**3,admission=account,preexec_admission=account,child_identity=who,child_pid=who['pid'],supervisor_pid=100,terminal_confirmation=dict(terminal=True,pid=who['pid'],status=0,finished_ns=start+70),completed_logs={'raw.log':bind(raw),'samples.jsonl':bind(samples)},decision_log_bound_bytes=(64 if stage=='audit' else 16)*1024**2,anonymous_preexec_baseline={'/model':1})
   records.append(r);save(folder/'receipt.json',r)
  return root,plans,records,dict(device=1,inode=2,acquired_ns=1,release_ns=10000,state='released',kernel_echild=True),src
 def verify(self,module,name,runner,root,plans,lease,src):
  kwargs={'wrapper_commit':'a'*40}
  if name=='verify_singleton_receipt' or not hasattr(module,'APPROVED'):kwargs['expected_source']=src
  with patch.dict(sys.modules,{'child_runner':runner}),patch.object(sys,'path',[str(HERE),str(OLD),str(REPO/'scripts'),*sys.path]):return getattr(module,name)(root,lease,plans,**kwargs)
 def test_complete_receipt_verifiers_accept_only_stage_specific_CPU_limits(self):
  for label,module,name,runner,count in self.verifiers:
   root,plans,records,lease,src=self.fixture(module,count)
   with self.subTest(verifier=label):self.verify(module,name,runner,root,plans,lease,src)
   for p,r in zip(plans,records):
    original=copy.deepcopy(r['handshake']['limits'])
    wrong=[60,60] if p['stage']=='audit' else [90,90]
    for cpu in [wrong,[CPU[p['stage']]-1,CPU[p['stage']]],[CPU[p['stage']],CPU[p['stage']]+1]]:
     r['handshake']['limits']['RLIMIT_CPU']=cpu;save(root/p['stage']/'receipt.json',r)
     with self.subTest(verifier=label,stage=p['stage'],wrong=cpu),self.assertRaisesRegex(RuntimeError,'Receipt limits differ'):self.verify(module,name,runner,root,plans,lease,src)
    r['handshake']['limits']=original;save(root/p['stage']/'receipt.json',r)
 def test_wall_memory_and_lifecycle_guards_unchanged(self):
  for label,_,runner in self.adapters:
   with self.subTest(adapter=label):
    self.assertEqual((runner.DEADLINE,runner.PREFLIGHT_DEADLINE,runner.INTERVAL),(90,300,.1))
    self.assertEqual((runner.STOP_HEADROOM,runner.RSS_STOP,runner.ANON_GROWTH_STOP),(1024**3,6*1024**3,3*1024**3))
    self.assertEqual(runner.LIMITS['RLIMIT_AS'],12*1024**3);self.assertEqual(runner.LIMITS['RLIMIT_CORE'],0)
 def test_receipt_verifiers_still_reject_incorrect_nonCPU_limits(self):
  for label,module,name,runner,count in self.verifiers:
   root,plans,records,lease,src=self.fixture(module,count)
   p,r=plans[-1],records[-1]
   for key,wrong in [('RLIMIT_AS',[13*1024**3]*2),('RLIMIT_FSIZE',[65*1024**2]*2),('RLIMIT_CORE',[1,1])]:
    original=copy.deepcopy(r['handshake']['limits']);r['handshake']['limits'][key]=wrong;save(root/p['stage']/'receipt.json',r)
    with self.subTest(verifier=label,limit=key),self.assertRaisesRegex(RuntimeError,'Receipt limits differ'):self.verify(module,name,runner,root,plans,lease,src)
    r['handshake']['limits']=original;save(root/p['stage']/'receipt.json',r)

if __name__=='__main__':
 with contextlib.ExitStack() as stack:
  for obj,names in [(subprocess,['Popen','run','check_output']),(os,['fork','execve','kill','killpg','waitpid','waitid']),(resource,['setrlimit','prlimit']),(fcntl,['flock']),(signal,['setitimer'])]:
   for name in names:stack.enter_context(patch.object(obj,name,forbidden))
  unittest.main(verbosity=2)
