"""Finite Python-only package-selection, staging and lock-reuse regressions.

No Lean, real production/planning, compiler/checker, common-lock acquisition,
rebuild, retrieval or memory diagnostics. Only private fixture files are locked.
"""
from pathlib import Path
import contextlib,copy,fcntl,json,os,resource,shutil,sys,types,unittest,uuid
from unittest.mock import patch
import authority
import contracts as c
import driver
import focused_audit
import lease
import package_plan
import package_selection as selection
import scope
import semantic_inventory
HERE=Path(__file__).resolve().parent
RUN=HERE/'test-evidence'/uuid.uuid4().hex;RUN.mkdir(parents=True)
SNAPSHOTS=RUN/'python-sources';SNAPSHOTS.mkdir()
for p in HERE.glob('*.py'):(SNAPSHOTS/(p.name+'.txt')).write_bytes(p.read_bytes())
EVENTS=[]
REAL_COMMON=Path('/tmp/distance-sparsification-single-compiler.lock')
PLAN_BUILDER=driver.make_production_plan

def put(path,data=b'synthetic object, not Lean'):
 p=Path(path);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return p
def forbidden(*args,**kwargs):raise AssertionError('Forbidden real production, planning, process, retrieval or memory diagnostic API')

class Packages(unittest.TestCase):
 def setUp(self):
  self.root=RUN/self._testMethodName;self.root.mkdir()
  self.fresh=self.root/'fresh';self.fresh.mkdir();self.accepted=self.root/'accepted';self.accepted.mkdir()
  self.dep=put(self.accepted/'LightEFTSpanners/VotingOutput.olean')
  self.deps={'LightEFTSpanners.VotingOutput':c.bind(self.dep)}
  self.target=self.fresh/Path(*c.TARGET.split('.')).with_suffix('.olean')
 def tearDown(self):EVENTS.append({'fixture':self._testMethodName,'directory':str(self.root),'synthetic':True})
 def prepare(self):self.target.parent.mkdir(parents=True,exist_ok=True)
 def test_first_empty_directory_masks_missing_leaf_without_fallback(self):
  self.prepare();(self.fresh/'LightEFTSpanners').mkdir()
  selected=selection.selected_path([self.fresh,self.accepted],'LightEFTSpanners.VotingOutput')
  self.assertEqual(selected,self.fresh/'LightEFTSpanners/VotingOutput.olean');self.assertFalse(selected.exists())
  with self.assertRaisesRegex(c.Rejected,'Package selection masks'):c.effective([self.fresh,self.accepted],self.deps,self.target,False)
 def test_root_olean_marker_masks_missing_leaf_without_fallback(self):
  self.prepare();put(self.fresh/'LightEFTSpanners.olean')
  with self.assertRaisesRegex(c.Rejected,'Package selection masks'):c.effective([self.fresh,self.accepted],self.deps,self.target,False)
 def test_reversing_original_shared_package_roots_hides_target(self):
  old='LightEFTSpanners.SuppliedForestGoodEvent';target=put(self.fresh/'LightEFTSpanners/SuppliedForestGoodEvent.olean')
  with patch.object(c,'TARGET',old),patch.object(selection,'TARGET',old):
   with self.assertRaisesRegex(c.Rejected,'Package selection masks'):c.effective([self.accepted,self.fresh],self.deps,target,True)
  self.assertEqual(selection.selected_path([self.accepted,self.fresh],old),self.accepted/'LightEFTSpanners/SuppliedForestGoodEvent.olean')
 def test_deeper_namespace_under_same_top_level_cannot_fix_both_orders(self):
  name='LightEFTSpanners.Stage.SuppliedForestGoodEvent';target=put(self.fresh/'LightEFTSpanners/Stage/SuppliedForestGoodEvent.olean')
  self.assertNotEqual(selection.selected_path([self.fresh,self.accepted],'LightEFTSpanners.VotingOutput'),self.dep)
  self.assertNotEqual(selection.selected_path([self.accepted,self.fresh],name),target)
 def test_distinct_top_level_selects_all_dependencies_and_target(self):
  self.prepare();before=c.effective([self.fresh,self.accepted],self.deps,self.target,False)
  put(self.target);put(self.target.with_suffix('.ir.sig'))
  after=c.effective([self.fresh,self.accepted],self.deps,self.target,True)
  for r in [before,after]:
   self.assertEqual(r['selected']['LightEFTSpanners.VotingOutput'],str(self.dep));self.assertEqual(r['selected'][c.TARGET],str(self.target))
 def test_duplicate_leaf_still_rejected_independently(self):
  self.prepare();put(self.fresh/'LightEFTSpanners/VotingOutput.olean')
  with self.assertRaisesRegex(c.Rejected,'Shadow/missing/wrong effective'):c.effective([self.fresh,self.accepted],self.deps,self.target,False)
 def test_wrong_root_sidecars_and_unknown_prefix_siblings_rejected(self):
  put(self.target)
  for suffix in c.SUFFIXES[1:]+('.ir.sig.hash','.unknown'):
   with self.subTest(suffix=suffix):
    wrong=put(self.accepted/Path(*c.TARGET.split('.')).with_suffix(suffix))
    try:
     with self.assertRaisesRegex(c.Rejected,'Target sidecar shadow'):c.effective([self.fresh,self.accepted],self.deps,self.target,True)
    finally:wrong.unlink()
 def test_predicted_layout_is_read_only_and_matches_actual_after_creation(self):
  absent=self.root/'future';target=absent/Path(*c.TARGET.split('.')).with_suffix('.olean')
  predicted=c.effective([absent,self.accepted],self.deps,target,False,predicted=True)
  self.assertFalse(absent.exists())
  put(target);actual=c.effective([absent,self.accepted],self.deps,target,True)
  self.assertEqual(predicted['selected'],actual['selected'])
 def test_predicted_original_layout_rejects_masking_before_any_write(self):
  absent=self.root/'future';old='LightEFTSpanners.SuppliedForestGoodEvent';target=absent/'LightEFTSpanners/SuppliedForestGoodEvent.olean'
  with patch.object(c,'TARGET',old),patch.object(selection,'TARGET',old):
   with self.assertRaisesRegex(c.Rejected,'Package selection masks'):c.effective([absent,self.accepted],self.deps,target,False,predicted=True)
  self.assertFalse(absent.exists())
 def test_predicted_root_olean_mask_is_modelled(self):
  selected=selection.selected_path([self.fresh,self.accepted],'LightEFTSpanners.VotingOutput',predicted_files=[self.fresh/'LightEFTSpanners.olean'])
  self.assertEqual(selected,self.fresh/'LightEFTSpanners/VotingOutput.olean')
 def test_symlink_package_marker_rejected(self):
  (self.fresh/'LightEFTSpanners').symlink_to(self.accepted/'LightEFTSpanners',target_is_directory=True)
  with self.assertRaisesRegex(c.Rejected,'Symlink package marker'):selection.selected_path([self.fresh,self.accepted],'LightEFTSpanners.VotingOutput')
 def test_actual_package_check_runs_before_each_child(self):
  evidence=self.root/'context-evidence';evidence.mkdir();work=self.root/'work';work.mkdir()
  roots=[self.fresh,self.accepted]
  plans=[{'stage':s,'argv':[sys.executable],'env':{'LEAN_PATH':':'.join(map(str,roots))},'sources':[]} for s in c.STAGES]
  fake=types.SimpleNamespace(file=None,acquired_ns=0,check=lambda:None)
  ctx=scope.Context(work,evidence,fake,plans,roots,self.deps,{str(self.dep):c.bind(self.dep)},fixture=True)
  self.prepare()
  for i,plan in enumerate(plans):
   with self.subTest(stage=plan['stage']):
    ctx.seen=plans[:i]
    if i and not self.target.exists():put(self.target);ctx.new=c.object_outputs(self.fresh,self.target,True)
    record={};ctx.before_child(plan,record,lambda:None)
    self.assertEqual(record['package_selection']['selected'][c.TARGET],str(self.target))
    # Empty directories do not change file-only inventory membership, so this
    # specifically exercises the added package check in the real hook.
    mask=self.fresh/'LightEFTSpanners';mask.mkdir()
    try:
     with self.assertRaisesRegex(c.Rejected,'Package selection masks'):ctx.before_child(plan,{},lambda:None)
    finally:mask.rmdir()
 def test_owner_resolver_checker_and_public_theorem_expectations(self):
  ci=self.root/'ci';ci.mkdir();loaded=['LightEFTSpanners.VotingOutput',c.TARGET]
  put(ci/'import-closure-loaded.txt',('\n'.join(loaded)+'\n').encode());put(ci/'strict-violations.txt',b'\n')
  put(ci/'actual-owner-inventory.tsv',f'owner\tname\tkind\tunsafe\tpartial\n{c.TARGET}\t{c.THEOREM}\ttheorem\tfalse\tfalse\n'.encode())
  put(ci/'recursive-dependencies.tsv',f'name\towner\tkind\ttypeDependencies\tbodyDependencies\tunsafe\tpartial\n{c.THEOREM}\t{c.TARGET}\ttheorem\t\tpropext\tfalse\tfalse\npropext\t[anonymous]\taxiom\t\t\tfalse\tfalse\n'.encode())
  raw='PASS: 1 new-module actual-owner declarations; 2 recursive constants, 0 opaque bodies; axioms [propext]\n'
  result=focused_audit.validate(ci,self.deps,raw);self.assertEqual(result['new_owner_roots'],1)
  self.assertEqual(c.THEOREM,'LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests')
  resolution=put(self.root/'resolution.json',json.dumps({'target':c.TARGET,'count':1,'resolved':[{'module':c.TARGET,'object':str(self.target)}],'search_path':[str(self.fresh),str(self.accepted)]}).encode())
  c.resolution(resolution,[self.fresh,self.accepted],self.target)
  wrong=json.loads(resolution.read_text());wrong['target']='LightEFTSpanners.SuppliedForestGoodEvent';resolution.write_text(json.dumps(wrong))
  with self.assertRaisesRegex(c.Rejected,'Official resolution mismatch'):c.resolution(resolution,[self.fresh,self.accepted],self.target)
 def test_exact_source_and_finite_proposal_no_limit_or_dependency_changes(self):
  base=json.loads((scope.DRAFT/'execution-proposal.json').read_text());spec=package_plan.expected_spec(base)
  self.assertEqual(spec,json.loads((HERE/'execution-proposal.json').read_text()))
  self.assertEqual(spec['profile'],base['profile']);self.assertEqual(spec['tool_hash_bindings'],base['tool_hash_bindings'])
  self.assertEqual(spec['accepted_project_objects'],base['accepted_project_objects'])
  self.assertNotEqual(spec['future_work_root'],base['future_work_root']);self.assertFalse(Path(spec['future_work_root']).exists())
  self.assertEqual(Path(spec['new_source']['path']).read_bytes(),Path(base['new_source']['path']).read_bytes())
  plans=semantic_inventory.build_expected(spec,Path(spec['future_work_root']),'a'*40)
  semantic_inventory.exact_commands(spec,Path(spec['future_work_root']),'a'*40,plans)
  self.assertEqual(plans[2]['argv'][-1],c.TARGET)
  sizes={p['stage']:len(json.dumps({'argv':p['argv'],'env':p['env'],'stage':p['stage']}).encode()) for p in plans}
  self.assertTrue(all(size<=4096 for size in sizes.values()),sizes)
  (self.root/'config-sizes.json').write_text(json.dumps(sizes,indent=2)+'\n')
 def test_complete_builder_calls_predicted_selection_with_synthetic_inputs(self):
  work=self.root/'future-work';objects=work/'objects'
  spec={'future_work_root':str(work),'environment':{'LEAN_PATH':str(objects)+':'+str(self.accepted),'LEAN_SYSROOT':'synthetic'},
   'commands':[{'stage':s,'argv':['not executed',s],'submitted_sources':[]} for s in c.STAGES]}
  classified={'semantic':{str(self.dep):c.bind(self.dep)},'excluded':{},'old_semantic_count':1,'signature_count':0,'excluded_count':0}
  fake=types.SimpleNamespace(scan=lambda:classified)
  with (patch.object(driver,'reviewed_inputs',return_value=(spec,{'bindings':[dict(self.deps['LightEFTSpanners.VotingOutput'],module='LightEFTSpanners.VotingOutput')]},{})) as reviewed,
       patch.object(driver,'reviewed_wrapper',return_value={}),patch.object(semantic_inventory,'load_inventory',return_value=(fake,{},{}))):
   bound=PLAN_BUILDER(work,'a'*40)
  reviewed.assert_called_once_with('a'*40)
  self.assertTrue(bound['predicted_package_selection']['predicted'])
  self.assertEqual(bound['predicted_package_selection']['selected']['LightEFTSpanners.VotingOutput'],str(self.dep))
  self.assertEqual(bound['predicted_package_selection']['selected'][c.TARGET],str(objects/Path(*c.TARGET.split('.')).with_suffix('.olean')))
  self.assertFalse(work.exists());self.assertEqual(bound['classification']['old_semantic_count'],1)

class Reuse(unittest.TestCase):
 def setUp(self):
  self.root=RUN/self._testMethodName;self.root.mkdir();self.directory=self.root/'owned';self.directory.mkdir()
  self.path=put(self.directory/'fixture.lock',b'preserve these bytes');self.path.chmod(0o600)
  s=self.path.stat();d=self.directory.stat();self.identity={'path':str(self.path),'device':s.st_dev,'inode':s.st_ino,'directory_identity':[d.st_dev,d.st_ino]}
  self.known={'identity':self.identity,'required_uid':os.getuid(),'required_mode':0o600,'released_epoch':'synthetic-prior-epoch'}
  self.authority=object.__new__(authority.ReviewedAuthority);self.authority.released_lock=self.known
  self.authority.check_live=lambda:None
  self.coord={'exclusive_worker':True,'same_directory':str(self.directory)}
  self.original=self.path.read_bytes();self.stack=contextlib.ExitStack();self.addCleanup(self.stack.close)
  self.stack.enter_context(patch.object(lease,'COMMON',self.path))
 def tearDown(self):
  self.stack.close();EVENTS.append({'fixture':self._testMethodName,'directory':str(self.root),'synthetic_private_lock_only':True})
 def instance(self):return lease.Lease(self.path,self.root/'lease.json',self.coord,fixture=False,authority=self.authority)
 def test_exact_released_inode_reused_without_create_truncate_or_unlink(self):
  opens=[];original_open=os.open
  def logged(path,flags,*args,**kwargs):
   if str(path)==self.path.name:
    opens.append(flags);self.assertEqual(flags&(os.O_CREAT|os.O_TRUNC|os.O_EXCL),0)
   return original_open(path,flags,*args,**kwargs)
  with patch.object(os,'open',logged):
   with self.instance() as owned:
    self.assertEqual(owned.identity,(self.identity['device'],self.identity['inode']));self.assertTrue(owned.record['reused_exact_released_inode'])
  self.assertEqual(len(opens),1);self.assertEqual(self.path.stat().st_ino,self.identity['inode']);self.assertEqual(self.path.read_bytes(),self.original)
  self.assertEqual(owned.record['state'],'released');self.assertTrue(owned.record['kernel_echild'])
 def test_contention_is_nonblocking_and_preserves_inode_and_bytes(self):
  with self.path.open('r+') as held:
   fcntl.flock(held,fcntl.LOCK_EX|fcntl.LOCK_NB)
   with self.assertRaises(BlockingIOError):self.instance().__enter__()
  self.assertEqual(self.path.stat().st_ino,self.identity['inode']);self.assertEqual(self.path.read_bytes(),self.original);self.assertFalse((self.root/'lease.json').exists())
 def test_different_inode_is_rejected_without_adoption(self):
  replacement=put(self.root/'replacement',self.original);replacement.chmod(0o600);os.replace(replacement,self.path)
  with self.assertRaisesRegex(c.Rejected,'inode differs'):self.instance().__enter__()
  self.assertFalse((self.root/'lease.json').exists());self.assertNotEqual(self.path.stat().st_ino,self.identity['inode'])
 def test_missing_lock_is_not_created(self):
  self.path.unlink()
  with self.assertRaises(FileNotFoundError):self.instance().__enter__()
  self.assertFalse(self.path.exists());self.assertFalse((self.root/'lease.json').exists())
 def test_fd_replacement_before_flock_is_rejected(self):
  real_open=os.open
  def replaced(name,flags,*args,**kwargs):
   fd=real_open(name,flags,*args,**kwargs)
   if str(name)==self.path.name:
    new=put(self.root/'replacement',self.original);new.chmod(0o600);os.replace(new,self.path)
   return fd
  with patch.object(os,'open',replaced):
   with self.assertRaisesRegex(c.Rejected,'Unsafe lock file|FD/path identity'):self.instance().__enter__()
  self.assertFalse((self.root/'lease.json').exists())
 def test_path_replacement_during_flock_is_rejected(self):
  real_flock=fcntl.flock
  def replaced(fd,flags):
   result=real_flock(fd,flags)
   new=put(self.root/'replacement',self.original);new.chmod(0o600);os.replace(new,self.path)
   return result
  with patch.object(fcntl,'flock',replaced):
   with self.assertRaisesRegex(c.Rejected,'Unsafe lock file|FD/path identity'):self.instance().__enter__()
  self.assertFalse((self.root/'lease.json').exists())
 def test_directory_replacement_during_flock_is_rejected(self):
  real_flock=fcntl.flock
  def replaced(fd,flags):
   result=real_flock(fd,flags);self.directory.rename(self.root/'old-owned');self.directory.mkdir()
   put(self.path,self.original).chmod(0o600);return result
  with patch.object(fcntl,'flock',replaced):
   with self.assertRaisesRegex(c.Rejected,'Lock directory replaced'):self.instance().__enter__()
  self.assertFalse((self.root/'lease.json').exists())
 def test_symlink_and_hardlink_are_not_adopted(self):
  backing=put(self.root/'backing',self.original);backing.chmod(0o600);self.path.unlink();self.path.symlink_to(backing)
  with self.assertRaisesRegex(c.Rejected,'Unsafe released lock'):self.instance().__enter__()
  self.path.unlink();os.link(backing,self.path)
  with self.assertRaisesRegex(c.Rejected,'Unsafe released lock'):self.instance().__enter__()
 def test_stale_coordination_rejected_before_lock_io(self):
  def stale():raise c.Rejected('Stale/future coordinated ownership document')
  self.authority.check_live=stale
  with patch.object(os,'open',side_effect=AssertionError('lock I/O before freshness rejection')):
   with self.assertRaisesRegex(c.Rejected,'Stale/future'):self.instance().__enter__()
 def test_reuse_requires_exact_explicit_coordinator_identity(self):
  commit='a'*40;facts={'synthetic':'owner facts'};known=authority.known_released_lock()
  doc={'approved_wrapper_commit':commit,'exclusive_worker':True,'reviewer_idle':True,'allow_new_epoch':True,'same_directory':'/tmp',
   'coordination_reference':'synthetic explicit reuse authority','facts':facts,'issued_ns':1,'allow_released_lock_reuse':True,'released_lock_identity':known['identity']}
  authority.check_document(doc,commit,facts,2)
  for key,value in [('allow_released_lock_reuse',False),('released_lock_identity',self.identity)]:
   bad=copy.deepcopy(doc);bad[key]=value
   with self.assertRaisesRegex(c.Rejected,'released-lock reuse'):authority.check_document(bad,commit,facts,2)
  with self.assertRaisesRegex(c.Rejected,'Stale/future'):authority.check_document(doc,commit,facts,60*10**9+1)

if __name__=='__main__':
 def guard(event,args):
  if event=='open' and isinstance(args[0],(str,bytes,os.PathLike)) and Path(os.fsdecode(args[0])).absolute()==REAL_COMMON:
   raise AssertionError('Actual common lock must not be opened during preparation')
 sys.addaudithook(guard)
 with contextlib.ExitStack() as stack:
  for obj,name in [(driver,'execute_production'),(driver,'make_production_plan'),(driver.subprocess,'Popen'),(driver.child_runner,'run_child'),
    (driver.child_runner,'VisibleAccounting'),(semantic_inventory.Inventory,'scan'),(os,'fork'),(os,'statvfs'),(shutil,'disk_usage'),
    (resource,'getrlimit'),(resource,'setrlimit'),(resource,'getrusage')]:stack.enter_context(patch.object(obj,name,forbidden))
  result=unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite([unittest.defaultTestLoader.loadTestsFromTestCase(Packages),unittest.defaultTestLoader.loadTestsFromTestCase(Reuse)]))
 c.save(RUN/'result.json',dict(tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),successful=result.wasSuccessful(),events=EVENTS,
  qualification='Python-only synthetic objects/audit rows/private lock fixtures; no Lean, real production, inventory scan, common-lock open/flock or memory diagnostic'))
 print('PACKAGE_FIXTURE_EVIDENCE='+str(RUN))
 sys.exit(0 if result.wasSuccessful() else 1)
