"""Preserved Python-only inventory fixtures; no children, locks or resource probes.

These call the real classifier/output APIs. They do not run legacy process
fixtures or the production entry, and do not establish Lean acceptance.
"""
from pathlib import Path
import contextlib,copy,fcntl,json,os,shutil,sys,types,unittest,uuid
from unittest.mock import patch
import contracts as c
import semantic_inventory as inv
import output_guards as guards
import driver
import lease
import scope

HERE=Path(__file__).resolve().parent
RUN=HERE/'test-evidence'/uuid.uuid4().hex
RUN.mkdir(parents=True)
SNAPSHOTS=RUN/'python-sources';SNAPSHOTS.mkdir()
for p in HERE.glob('*.py'):(SNAPSHOTS/(p.name+'.txt')).write_bytes(p.read_bytes())
EVENTS=[]

def put(path,data=b'fixture'):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data);return path

class InventoryTests(unittest.TestCase):
 def setUp(self):
  self.root=RUN/self._testMethodName;self.root.mkdir()
  self.inputs=self.root/'inputs';self.inputs.mkdir()
  self.olean=put(self.inputs/'Fixture/Module.olean',b'old object')
  self.ir=put(self.inputs/'Fixture/Module.ir',b'old IR')
  self.native=put(self.inputs/'libFixture.so',b'old native library')
  self.sig=put(self.inputs/'Fixture/Module.ir.sig',b'new local signature')
  self.prior={str(p):c.bind(p) for p in [self.olean,self.ir,self.native]}
  self.policy={'exact_static_archives':sorted(inv.ARCHIVES)}
  self.diagnosis=[]
  for suffix in inv.METADATA_FORMS:
   p=put(self.inputs/('Fixture/Module'+suffix),b'not semantic: '+suffix.encode())
   self.diagnosis.append({'path':str(p)})
  self.supplement=inv.capture_signatures(self.prior,[self.inputs])
 def inventory(self):
  return inv.Inventory(self.prior,self.supplement,self.policy,self.diagnosis,[self.inputs])
 def reject(self,pattern):
  return self.assertRaisesRegex(c.Rejected,pattern)
 def tearDown(self):
  EVENTS.append({'fixture':self._testMethodName,'preserved_directory':str(self.root)})
 def test_capture_and_semantic_classification(self):
  self.assertEqual(len(self.supplement),1)
  row=self.supplement[0]
  self.assertEqual(row['qualification'],inv.QUALIFICATION)
  self.assertEqual(row['module'],'Fixture.Module')
  self.assertEqual(row['sha256'],c.sha(self.sig.read_bytes()))
  self.assertEqual(row['identity'],c.signature(self.sig.stat()))
  self.assertEqual(row['bytes'],len(self.sig.read_bytes()))
  self.assertEqual(row['family'],{'olean':{'path':str(self.olean),'sha256':self.prior[str(self.olean)]['sha256']},'ir':{'path':str(self.ir),'sha256':self.prior[str(self.ir)]['sha256']}})
  result=self.inventory().scan()
  self.assertEqual(set(result['semantic']),set(self.prior)|{str(self.sig)})
  self.assertEqual((result['old_semantic_count'],result['signature_count'],result['excluded_count']),(3,1,7))
  self.assertEqual(result['members'][str(self.inputs)],set(result['semantic'])|set(result['excluded']))
  self.assertNotIn(str(self.sig)+'.hash',result['semantic'])
  self.assertIn(str(self.sig)+'.hash',result['excluded'])
 def test_missing_signature_rejected(self):
  self.sig.unlink()
  with self.reject('Missing/new signature'):self.inventory().scan()
 def test_changed_signature_hash_rejected(self):
  self.sig.write_bytes(b'changed signature')
  with self.reject('Input hash drift'):self.inventory().scan()
 def test_replaced_equal_signature_identity_rejected(self):
  other=put(self.root/'replacement',self.sig.read_bytes());os.replace(other,self.sig)
  with self.reject('Signature identity changed'):self.inventory().scan()
 def test_new_signature_rejected_even_in_known_family(self):
  other=put(self.inputs/'Fixture/Other.olean');ir=put(self.inputs/'Fixture/Other.ir')
  self.prior.update({str(p):c.bind(p) for p in [other,ir]})
  put(self.inputs/'Fixture/Other.ir.sig')
  with self.reject('New/unreviewed signature'):self.inventory().scan()
 def test_bad_signature_binding_and_duplicate_rejected(self):
  original=copy.deepcopy(self.supplement)
  for field,value,pattern in [('module','Wrong.Module','association'),('qualification','historically authenticated','qualification'),('family',{},'association')]:
   with self.subTest(field=field):
    self.supplement=copy.deepcopy(original);self.supplement[0][field]=value
    with self.reject(pattern):self.inventory()
  self.supplement=original*2
  with self.reject('Duplicate signature'):self.inventory()
 def test_missing_old_ir_family_rejected(self):
  self.prior.pop(str(self.ir))
  with self.reject('no old bound IR'):self.inventory()
 def test_signature_expected_length_rejected(self):
  self.supplement[0]['bytes']+=1
  with self.reject('Input length drift'):self.inventory().scan()
 def test_all_excluded_files_metadata_only_even_if_changed(self):
  excluded={r['path'] for r in self.diagnosis}
  for p in excluded:Path(p).write_bytes(b'changed metadata contents and length')
  original_open=os.open;original_read=Path.read_bytes
  def no_open(path,*args,**kwargs):
   self.assertNotIn(str(path),excluded,'excluded content was opened')
   return original_open(path,*args,**kwargs)
  def no_read(path,*args,**kwargs):
   self.assertNotIn(str(path),excluded,'excluded content was read')
   return original_read(path,*args,**kwargs)
  with patch.object(os,'open',no_open),patch.object(Path,'read_bytes',no_read):result=self.inventory().scan()
  for row in result['excluded'].values():
   self.assertTrue(row['metadata_only']);self.assertNotIn('sha256',row)
   self.assertEqual(row['link_count'],1)
 def test_missing_or_new_metadata_path_rejected(self):
  victim=Path(self.diagnosis[0]['path']);data=victim.read_bytes();victim.unlink()
  with self.reject('Excluded-file membership'):self.inventory().scan()
  put(victim,data);put(self.inputs/'Fixture/Unknown.olean.hash')
  with self.reject('Unknown search input'):self.inventory().scan()
 def test_unknown_diagnosed_hash_form_and_family_rejected(self):
  for name,pattern in [('Fixture/Module.hash','Unknown diagnosed'),('Fixture/Unknown.olean.hash','Unbound module family')]:
   with self.subTest(name=name):
    extra={'path':str(self.inputs/name)}
    with self.reject(pattern):inv.Inventory(self.prior,self.supplement,self.policy,self.diagnosis+[extra],[self.inputs])
 def test_unknown_native_archive_and_hash_rejected(self):
  for name in ['extra.so','extra.a','Fixture/Module.unknown.hash','extra.dll','extra.dylib']:
   with self.subTest(name=name):
    p=put(self.inputs/name)
    try:
     with self.reject('Unknown search input'):self.inventory().scan()
    finally:p.unlink()
 def test_old_hash_native_and_ir_bindings_remain_authoritative(self):
  old_hash=Path(self.diagnosis[0]['path']);self.prior[str(old_hash)]=c.bind(old_hash)
  result=self.inventory().scan()
  self.assertIn(str(old_hash),result['semantic']);self.assertNotIn(str(old_hash),result['excluded'])
  for p in [self.olean,self.ir,self.native,old_hash]:
   with self.subTest(path=str(p)):
    data=p.read_bytes();p.write_bytes(b'old binding must fail')
    try:
     with self.reject('Input hash drift'):self.inventory().scan()
    finally:p.write_bytes(data)
 def test_old_semantic_deletion_rejected(self):
  self.native.unlink()
  with self.reject('Missing old bound'):self.inventory().scan()
 def test_symlink_hardlink_and_fifo_rejected_for_signature_and_exclusion(self):
  for target in [self.sig,Path(self.diagnosis[0]['path'])]:
   original=target.read_bytes()
   for kind in ['symlink','hardlink','fifo']:
    with self.subTest(target=str(target),kind=kind):
     backing=put(self.root/'backing',original);target.unlink()
     if kind=='symlink':target.symlink_to(backing)
     elif kind=='hardlink':os.link(backing,target)
     else:os.mkfifo(target)
     try:
      with self.reject('Nonregular/linked'):self.inventory().scan()
     finally:target.unlink();backing.unlink();put(target,original)
   # Restore the signature identity binding for the next target's tests.
   self.supplement=inv.capture_signatures(self.prior,[self.inputs])
 def test_symlink_parent_and_search_root_rejected(self):
  linked=self.root/'linked';linked.symlink_to(self.inputs,target_is_directory=True)
  with self.reject('Invalid search root'):list(inv.walk_files(linked))
  with self.reject('Symlink input parent'):inv.inspect_metadata(linked/'Fixture/Module.ir.sig')
 def test_exact_ten_archives_are_metadata_only_and_extra_is_rejected(self):
  # Synthetic enumeration at the exact production paths. Never open/touch the
  # real toolchain archives; real metadata enumeration is exercised by the plan.
  root=Path('/workspace/toolchains/lean-4.34.0-linux/lib/lean')
  diagnosis=[{'path':p} for p in sorted(inv.ARCHIVES)]
  inventory=inv.Inventory({},[],self.policy,diagnosis,[root])
  rows=[(Path(p),{'path':p,'metadata_only':True,'bytes':7}) for p in sorted(inv.ARCHIVES)]
  with patch.object(inv,'walk_files',return_value=iter(rows)),patch.object(inv,'bind',side_effect=AssertionError('archive content read')):
   result=inventory.scan()
  self.assertEqual(set(result['excluded']),inv.ARCHIVES)
  self.assertEqual(result['semantic'],{})
  extra=root/'libUnknown.a'
  with patch.object(inv,'walk_files',return_value=iter(rows+[(extra,{'path':str(extra)})])):
   with self.reject('Unknown search input'):inventory.scan()
  wrong=copy.deepcopy(self.policy);wrong['exact_static_archives'].append(str(extra))
  with self.reject('ten exact'):inv.Inventory({},[],wrong,diagnosis,[root])
 def test_old_archive_binding_is_never_downgraded(self):
  root=Path('/workspace/toolchains/lean-4.34.0-linux/lib/lean')
  archive=sorted(inv.ARCHIVES)[0]
  old={archive:{'path':archive,'sha256':'0'*64}}
  inventory=inv.Inventory(old,[],self.policy,[{'path':p} for p in sorted(inv.ARCHIVES)],[root])
  self.assertNotIn(archive,inventory.excluded)
  rows=[(Path(p),{'path':p,'metadata_only':True}) for p in sorted(inv.ARCHIVES)]
  calls=[]
  def old_bind(path,expected):
   calls.append(str(path));self.assertEqual(expected,old[archive]);raise c.Rejected('Old archive hash mismatch')
  with patch.object(inv,'walk_files',return_value=iter(rows)),patch.object(inv,'bind',side_effect=old_bind):
   with self.reject('Old archive hash mismatch'):inventory.scan()
  self.assertEqual(calls,[archive])
 def test_ambiguous_module_family_roots_rejected(self):
  with self.reject('Ambiguous module'):inv.family(self.sig,'.ir.sig',[self.inputs,self.root],self.prior)
 def test_signature_only_target_shadow_rejected(self):
  roots=[self.root/'new',self.root/'other'];[p.mkdir() for p in roots]
  target=roots[0]/Path(*c.TARGET.split('.')).with_suffix('.olean')
  shadow=put(roots[1]/Path(*c.TARGET.split('.')).with_suffix('.ir.sig'))
  with self.reject('Target sidecar shadow'):c.effective(roots,{},target,False)
  shadow.unlink();put(target);put(roots[1]/Path(*c.TARGET.split('.')).with_suffix('.ir.sig'))
  with self.reject('Target sidecar shadow'):c.effective(roots,{},target,True)
 def test_existing_module_shadow_rejected(self):
  other=self.root/'other';other.mkdir();put(other/'Fixture/Module.olean')
  target=self.root/'new/LightEFTSpanners/SuppliedForestGoodEvent.olean'
  with self.reject('Shadow/missing/wrong effective'):c.effective([self.inputs,other],{'Fixture.Module':self.prior[str(self.olean)]},target,False)
 def test_signature_outputs_captured_and_hash_sidecar_rejected(self):
  root=self.root/'objects';root.mkdir()
  target=put(root/Path(*c.TARGET.split('.')).with_suffix('.olean'),b'new target')
  sig=put(target.with_suffix('.ir.sig'),b'new signature')
  self.assertIn(str(sig),guards.live_objects(root,target,True))
  captured=c.object_outputs(root,target,True);self.assertIn(str(sig),captured)
  sig.write_bytes(b'changed after completion')
  with self.reject('Bound input identity/content changed'):c.unchanged(captured)
  sidecar=put(target.with_suffix('.ir.sig.hash'))
  with self.reject('Unexpected live output path'):guards.live_objects(root,target,True)
  with self.reject('Unexpected new object'):c.object_outputs(root,target,True)
  sidecar.unlink()
 def test_generated_signature_links_rejected(self):
  root=self.root/'objects';root.mkdir()
  target=put(root/Path(*c.TARGET.split('.')).with_suffix('.olean'))
  backing=put(self.root/'backing')
  target.with_suffix('.ir.sig').symlink_to(backing)
  with self.reject('Nonregular/linked live output'):guards.live_objects(root,target,True)
  with self.reject('Symlink in output tree'):c.object_outputs(root,target,True)
 def test_exact_approved_argv_environment_and_sysroot(self):
  spec=json.loads((driver.DRAFT/'execution-proposal.json').read_text());work=Path(spec['future_work_root']);commit='a'*40
  plans=inv.build_expected(spec,work,commit);inv.exact_commands(spec,work,commit,plans)
  for mutate in ['argv','sysroot','extra_env','path','threads','linker']:
   with self.subTest(mutate=mutate):
    bad=copy.deepcopy(plans)
    if mutate=='argv':bad[0]['argv'].append('--run')
    if mutate=='sysroot':bad[0]['env']['LEAN_SYSROOT']='/other'
    if mutate=='extra_env':bad[0]['env']['LD_PRELOAD']='/extra.so'
    if mutate=='path':bad[0]['env']['LEAN_PATH']+=':/extra'
    if mutate=='threads':bad[2]['env']['LEAN_NUM_THREADS']='2'
    if mutate=='linker':bad[0]['argv'][0]='/usr/bin/cc'
    with self.reject('Changed exact argv/environment'):inv.exact_commands(spec,work,commit,bad)
  altered=copy.deepcopy(spec);altered['environment']['LEAN_SYSROOT']='/other'
  with self.reject('Pinned LEAN_SYSROOT'):inv.exact_commands(altered,work,commit,inv.build_expected(altered,work,commit))
  altered=copy.deepcopy(spec);altered['commands'][0]['argv'][0]='/usr/bin/cc'
  with self.reject('Archive exclusion forbids'):inv.exact_commands(altered,work,commit,inv.build_expected(altered,work,commit))
  with self.reject('Work root differs'):inv.exact_commands(spec,work/'changed',commit,plans)
 def context(self):
  work=self.root/'work';work.mkdir();objects=work/'objects';objects.mkdir()
  evidence=self.root/'evidence';evidence.mkdir()
  roots=[objects,self.inputs]
  plans=[{'stage':stage,'sources':[],'argv':[],'env':{'LEAN_PATH':':'.join(map(str,roots))}} for stage in c.STAGES]
  inventory=self.inventory();classified=inventory.scan()
  fake_lease=types.SimpleNamespace(file=None,acquired_ns=0,check=lambda:None)
  reference={'qualification':inv.QUALIFICATION,'fixture':'separate supplement reference'}
  # Replace only Git/data loading with an already constructed synthetic
  # inventory. Context's classification, journals, effective lookup, binding,
  # receipt hooks and output capture remain the production implementations.
  with patch.object(inv,'load_inventory',return_value=(inventory,{},reference)):
   context=scope.Context(work,evidence,fake_lease,plans,roots,{'Fixture.Module':self.prior[str(self.olean)]},classified['semantic'],fixture=False,wrapper_commit='a'*40)
  return context,plans,reference
 def test_context_signature_reference_and_preservation(self):
  context,plans,reference=self.context();context.verify(False)
  (context.evidence/'compile').mkdir();record={}
  context.before_child(plans[0],record,lambda:None)
  self.assertEqual(record['signature_supplement'],reference)
  self.assertEqual(record['excluded_initial_metadata'],context.excluded_ref)
  rows=[json.loads(line) for line in Path(context.excluded_ref['path']).read_text().splitlines()]
  self.assertEqual(len(rows),7);self.assertTrue(all('sha256' not in row for row in rows))
  self.sig.write_bytes(b'changed accepted signature')
  with self.reject('Bound input identity/content changed'):context.verify(False)
 def test_context_membership_and_metadata_journal_preservation(self):
  context,_,_=self.context()
  Path(self.diagnosis[0]['path']).write_bytes(b'metadata content can change without hashing')
  context.verify(False)
  put(self.inputs/'extra.a')
  with self.reject('Unknown search input'):context.verify(False)
  (self.inputs/'extra.a').unlink()
  Path(context.excluded_ref['path']).write_text('tampered initial enumeration')
  with self.reject('Initial excluded metadata journal changed'):context.verify(False)
 def test_context_captures_signature_then_rejects_completed_mutation(self):
  context,plans,_=self.context();put(context.target);sig=put(context.target.with_suffix('.ir.sig'))
  context.after_child(plans[0],{'exit':0},lambda:None)
  self.assertIn(str(sig),context.new);context.verify(True)
  sig.write_bytes(b'completed signature changed')
  with self.reject('Bound input identity/content changed'):context.verify(True)
 def test_context_final_metadata_exports_reconstruct(self):
  context,plans,_=self.context();put(context.target);put(context.target.with_suffix('.ir.sig'))
  context.new=c.object_outputs(context.objects,context.target,True)
  context.seen=plans
  # Exercise only finish/export wiring with deliberately synthetic audit data;
  # no audit validation, compiler, child lifecycle or lock is simulated here.
  context.audit_result={'fixture_only':True}
  for name in c.EXPORTS:put(context.audit/name,b'synthetic fixture export\n')
  put(context.evidence/'audit/raw.log',b'synthetic fixture, not Lean diagnostics\n')
  result=context.finish()
  self.assertEqual(set(result['excluded_metadata_exports']),{'initial','final'})
  for label in ['initial','final']:
   source=context.evidence/('excluded-metadata-'+label+'.jsonl')
   directory=context.evidence/('excluded-'+label+'-export')
   scope.verify_chunks(directory,source)
  self.assertEqual(result['signature_supplement'],context.signature_ref)

def forbidden(*args,**kwargs):raise AssertionError('Forbidden child/lock/resource/production API during inventory fixtures')

if __name__=='__main__':
 # Hard fail if these fixtures drift into the legacy process harness.
 with contextlib.ExitStack() as stack:
  for obj,name in [(driver,'execute_production'),(driver,'run_fixture'),(lease.Lease,'__enter__'),(fcntl,'flock'),(os,'fork'),(os,'statvfs'),(shutil,'disk_usage'),(driver.subprocess,'Popen')]:
   stack.enter_context(patch.object(obj,name,forbidden))
  suite=unittest.defaultTestLoader.loadTestsFromTestCase(InventoryTests)
  result=unittest.TextTestRunner(verbosity=2).run(suite)
 c.save(RUN/'result.json',{'tests':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),'successful':result.wasSuccessful(),'events':EVENTS,'no_child_or_lock_or_resource_probe':True})
 print('FIXTURE_EVIDENCE='+str(RUN))
 sys.exit(0 if result.wasSuccessful() else 1)
