"""Synthetic activation-order tests. No real planning, production, lock or probes.

The production entry's ordering logic is called only with a fake commit, fake
planner, controlled ownership facts and virtual clock. Fresh-flow filesystem
and lease/batch calls are intercepted in memory. Stale flows must never reach
those intercepts. This does not grant or simulate production acceptance.
"""
from pathlib import Path
import contextlib,copy,fcntl,io,json,os,resource,shutil,sys,unittest,uuid
from unittest.mock import patch
import authority
import contracts as c
import driver
import lease
import scope
import semantic_inventory

HERE=Path(__file__).resolve().parent
RUN=HERE/'test-evidence'/uuid.uuid4().hex;RUN.mkdir(parents=True)
SNAPSHOTS=RUN/'python-sources';SNAPSHOTS.mkdir()
for p in HERE.glob('*.py'):(SNAPSHOTS/(p.name+'.txt')).write_bytes(p.read_bytes())
EVENTS=[]
SECOND=10**9

class ActivationTests(unittest.TestCase):
 def setUp(self):
  self.root=RUN/self._testMethodName;self.root.mkdir()
  self.work=self.root/'work';self.evidence=self.root/'production-evidence'
  self.claim=self.root/'production-invocation-claimed.json'
  self.clock=SECOND;self.events=[];self.mutations=[];self.provider_calls=0
  self.commit='a'*40
  self.facts={'owner_pid':123,'owner_start_ticks':'synthetic-start','boot_id':'synthetic-boot','namespaces':{'pid':'synthetic-pid','mnt':'synthetic-mnt','cgroup':'synthetic-cgroup'},'directory_identity':[7,11]}
  self.wrapper={'synthetic.py':{'path':'synthetic.py','sha256':'b'*64,'bytes':17,'identity':[7,12,17,1,1]}}
  self.bound={'plans':[{'stage':s,'env':{'LEAN_SYSROOT':'synthetic unchanged'},'argv':['synthetic never executed',s]} for s in c.STAGES],
   'roots':[self.work/'objects',self.root/'existing-inputs'],'dependencies':{'Synthetic.Module':{'sha256':'c'*64}},'inputs':copy.deepcopy(self.wrapper)}
  self.original_bound=copy.deepcopy(self.bound)
  self.planning_delay=96*SECOND;self.review_delay=0;self.idle_delay=0
  self.change_facts=False;self.bad_wrapper=False;self.provider_delay=0
  self.old_document=None;self.plan_failure=False;self.document=None
  self.stack=contextlib.ExitStack();self.addCleanup(self.stack.close)
  for obj,name,value in [(driver,'HERE',self.root),(driver,'reviewed_inputs',self.inputs),(driver,'make_production_plan',self.plan),
    (scope,'reviewed_wrapper',self.review),(authority,'facts',self.current_facts),(driver.time,'monotonic_ns',lambda:self.clock),
    (driver.child_runner,'assert_idle',self.idle),(driver,'Lease',self.virtual_lease),(driver,'_run_batch',self.virtual_batch)]:
   self.stack.enter_context(patch.object(obj,name,value))
 def tearDown(self):
  self.stack.close()
  row={'fixture':self._testMethodName,'synthetic':True,'events':self.events,'virtual_mutations':self.mutations,
   'provider_calls':self.provider_calls,'claim_exists':self.claim.exists(),'work_exists':self.work.exists(),'evidence_exists':self.evidence.exists()}
  (self.root/'events.json').write_text(json.dumps(row,indent=2)+'\n');EVENTS.append(row)
 def inputs(self):
  self.events.append('read-only inputs')
  return {'future_work_root':str(self.work)},None,None
 def plan(self,work,commit):
  self.assertEqual((work,commit),(self.work,self.commit));self.assert_no_mutations()
  self.assertEqual(self.provider_calls,0)
  self.events.append('planning starts');self.clock+=self.planning_delay;self.events.append('planning finished')
  if self.plan_failure:raise c.Rejected('Synthetic planning failure')
  return self.bound
 def current_facts(self):
  self.events.append('current facts checked');return copy.deepcopy(self.facts)
 def review(self,commit):
  self.assertEqual(commit,self.commit);self.events.append('wrapper bindings checked');self.clock+=self.review_delay
  return {} if self.bad_wrapper else copy.deepcopy(self.wrapper)
 def idle(self,*args):
  self.events.append('idle check');self.clock+=self.idle_delay
  if self.change_facts:self.facts['owner_start_ticks']='changed incarnation'
 def fresh_document(self):
  return {'approved_wrapper_commit':self.commit,'exclusive_worker':True,'reviewer_idle':True,'allow_new_epoch':True,'same_directory':'/tmp',
   'coordination_reference':'synthetic coordinator only; not real authority','facts':copy.deepcopy(self.facts),'issued_ns':self.clock}
 def provider(self):
  self.assert_no_mutations();self.assertEqual(self.events[-1],'planning finished')
  self.provider_calls+=1;self.events.append('coordinator called after planning')
  self.document=self.old_document if self.old_document is not None else self.fresh_document()
  self.clock+=self.provider_delay
  return self.document
 def virtual_lease(self,*args,**kwargs):
  self.events.append('virtual lease constructed')
  self.assertEqual(args[:3],(lease.COMMON,self.evidence/'lease.json',self.document))
  self.assertFalse(kwargs['fixture']);self.assertIsInstance(kwargs['authority'],authority.ReviewedAuthority)
  return ('virtual lease, never acquired',)
 def virtual_batch(self,work,evidence,plans,roots,dependencies,inputs,lease_arg,fixture,commit):
  self.events.append('virtual batch reached; no execution')
  self.assertEqual((work,evidence,fixture,commit),(self.work,self.evidence,False,self.commit))
  for actual,key in [(plans,'plans'),(roots,'roots'),(dependencies,'dependencies'),(inputs,'inputs')]:
   self.assertIs(actual,self.bound[key]);self.assertEqual(actual,self.original_bound[key])
  self.assertEqual(lease_arg,('virtual lease, never acquired',))
  return {'synthetic':True,'no_child_or_lease_execution':True}
 def assert_no_mutations(self):
  self.assertFalse(self.claim.exists());self.assertFalse(self.work.exists());self.assertFalse(self.evidence.exists());self.assertEqual(self.mutations,[])
 def reject(self,pattern):
  with self.assertRaisesRegex(c.Rejected,pattern):driver.execute_production(self.commit,self.provider)
  self.assert_no_mutations();self.assertNotIn('virtual lease constructed',self.events)
 def test_long_planning_then_fresh_coordination_and_exact_plan_forwarding(self):
  # Intercept all activation writes; none creates an actual claim/work/lock.
  original_mkdir=Path.mkdir;original_open=Path.open;claim_io=io.StringIO()
  def mkdir(path,*args,**kwargs):
   if path in [self.work,self.evidence,self.work/'objects']:
    self.assertEqual(self.events[-1] if not self.mutations else '', 'current facts checked' if not self.mutations else '')
    self.mutations.append('virtual mkdir '+str(path));return
   return original_mkdir(path,*args,**kwargs)
  @contextlib.contextmanager
  def claim_open(path,*args,**kwargs):
   if path==self.claim:
    self.assertEqual(args[0],'x');self.mutations.append('virtual claim write');yield claim_io
   else:
    with original_open(path,*args,**kwargs) as f:yield f
  with patch.object(Path,'mkdir',mkdir),patch.object(Path,'open',claim_open):
   result=driver.execute_production(self.commit,self.provider)
  self.assertTrue(result['synthetic']);self.assertEqual(self.provider_calls,1)
  self.assertGreater(self.document['issued_ns'],60*SECOND)
  self.assertEqual(json.loads(claim_io.getvalue())['coordination'],self.document)
  self.assertEqual(self.events.count('planning starts'),1)
  self.assertEqual(self.events.count('current facts checked'),2)
  self.assertEqual(self.mutations,['virtual mkdir '+str(self.evidence),'virtual claim write','virtual mkdir '+str(self.work),'virtual mkdir '+str(self.work/'objects')])
  self.assertFalse(self.claim.exists());self.assertFalse(self.work.exists());self.assertFalse(self.evidence.exists())
 def test_preissued_document_returned_after_delayed_planning_creates_nothing(self):
  self.old_document=self.fresh_document();issued=self.old_document['issued_ns']
  self.reject('issued after planning')
  self.assertEqual(self.old_document['issued_ns'],issued);self.assertEqual(self.provider_calls,1)
 def test_postplanning_document_expired_in_provider_creates_nothing(self):
  self.provider_delay=60*SECOND;self.reject('Stale/future')
  self.assertEqual(self.provider_calls,1);self.assertEqual(self.document['issued_ns'],97*SECOND)
 def test_expiry_during_wrapper_binding_check_creates_nothing(self):
  self.review_delay=60*SECOND;self.reject('Stale/future');self.assertEqual(self.provider_calls,1)
 def test_expiry_during_idle_check_creates_nothing(self):
  self.idle_delay=60*SECOND;self.reject('Stale/future');self.assertIn('idle check',self.events);self.assertEqual(self.provider_calls,1)
 def test_changed_ownership_after_authority_construction_creates_nothing(self):
  self.change_facts=True;self.reject('incarnation differs');self.assertEqual(self.provider_calls,1)
 def test_wrapper_binding_mismatch_creates_nothing(self):
  # A missing helper in the exact prepared input set cannot be compensated by
  # new authority data; the prepared object is never regenerated or mutated.
  self.bound['inputs']={}
  self.reject('Wrapper bindings missing');self.assertEqual(self.provider_calls,1)
 def test_planning_failure_does_not_request_coordination_or_create_anything(self):
  self.plan_failure=True;self.reject('Synthetic planning failure');self.assertEqual(self.provider_calls,0)
 def test_document_argument_is_not_silently_reissued(self):
  document=self.fresh_document();before=copy.deepcopy(document)
  with self.assertRaisesRegex(c.ProductionDisabled,'post-planning coordination provider'):driver.execute_production(self.commit,document)
  self.assertEqual(document,before);self.assertEqual(self.events,[]);self.assert_no_mutations()
 def test_missing_coordination_and_wrong_flags_still_disabled(self):
  with self.assertRaises(c.ProductionDisabled):driver.execute_production(self.commit)
  with self.assertRaises(c.ProductionDisabled):driver.execute_production(self.commit,self.provider,enabled=True)
  self.assertEqual(self.events,[]);self.assert_no_mutations()
 def test_timeout_boundary_unchanged(self):
  doc=self.fresh_document()
  authority.check_document(doc,self.commit,self.facts,self.clock+60*SECOND-1)
  with self.assertRaisesRegex(c.Rejected,'Stale/future'):authority.check_document(doc,self.commit,self.facts,self.clock+60*SECOND)
  self.assert_no_mutations()
 def test_real_lease_rechecks_stale_authority_before_any_lock_io(self):
  doc=self.fresh_document();real_authority=authority.ReviewedAuthority(self.commit,doc)
  current_lease=lease.Lease(lease.COMMON,self.root/'unused-lease.json',doc,fixture=False,authority=real_authority)
  self.clock+=60*SECOND
  with self.assertRaisesRegex(c.Rejected,'Stale/future'):current_lease.__enter__()
  self.assertIsNone(current_lease.file);self.assert_no_mutations()

def forbidden(*args,**kwargs):raise AssertionError('Real inventory/process/lock/resource API forbidden in synthetic activation fixture')

if __name__=='__main__':
 with contextlib.ExitStack() as stack:
  for obj,name in [(driver,'reviewed_inputs'),(driver,'make_production_plan'),(scope,'reviewed_wrapper'),(authority,'facts'),
    (semantic_inventory.Inventory,'scan'),(semantic_inventory,'load_inventory'),(driver.subprocess,'Popen'),
    (driver.child_runner,'run_child'),(driver.child_runner,'VisibleAccounting'),(fcntl,'flock'),(os,'open'),(os,'fork'),
    (os,'statvfs'),(os,'sysconf'),(shutil,'disk_usage'),(resource,'getrlimit'),(resource,'setrlimit'),(resource,'getrusage')]:
   stack.enter_context(patch.object(obj,name,forbidden))
  result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ActivationTests))
 c.save(RUN/'result.json',dict(tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),successful=result.wasSuccessful(),events=EVENTS,
  qualification='Synthetic delayed planner/virtual clock/ownership/activation effects only; no real inventory, production, lock, resource probe or Lean'))
 print('ACTIVATION_FIXTURE_EVIDENCE='+str(RUN))
 sys.exit(0 if result.wasSuccessful() else 1)
