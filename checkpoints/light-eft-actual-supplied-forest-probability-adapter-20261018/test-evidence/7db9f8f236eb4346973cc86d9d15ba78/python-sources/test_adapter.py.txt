"""Python-only synthetic adapter regressions. No Lean, real inventory or lease.

Real approved JSON is translated. Files used as objects/audit data are private
synthetic fixtures. Activation ordering is exercised only with stub planning,
fake ownership/time and an expired document; it cannot reach mutation/locking.
"""
from pathlib import Path
import contextlib,copy,fcntl,json,os,resource,shutil,sys,types,unittest,uuid
from unittest.mock import patch
import authority
import contracts as c
import driver
import focused_audit as audit
import lease
import probability_plan as pp
import scope
import semantic_inventory as inventory
HERE=Path(__file__).resolve().parent
RUN=HERE/'test-evidence'/uuid.uuid4().hex;RUN.mkdir(parents=True)
snapshots=RUN/'python-sources';snapshots.mkdir()
for p in HERE.glob('*.py'):(snapshots/(p.name+'.txt')).write_bytes(p.read_bytes())
RAW=json.loads((pp.DRAFT_DIR/'focused-validation-plan.json').read_text())
DEPS=json.loads((pp.DRAFT_DIR/'project-dependency-bindings.json').read_text())['dependencies']
BUILD=driver.make_production_plan
SCAN=inventory.Inventory.scan
EVENTS=[]
def put(path,data=b'synthetic only, not Lean'):
 p=Path(path);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return p
def forbidden(*args,**kwargs):raise AssertionError('Forbidden real compiler/production/inventory/lock/resource API in synthetic fixtures')

class Adapter(unittest.TestCase):
 def setUp(self):
  self.root=RUN/self._testMethodName;self.root.mkdir();self.commit='a'*40
 def tearDown(self):EVENTS.append(dict(fixture=self._testMethodName,directory=str(self.root),synthetic=True))
 def translated(self):return pp.translate_commands(pp.normalize_plan(copy.deepcopy(RAW)),Path(RAW['future_work_root']),self.commit)
 def test_real_plan_translation_preserves_every_role_field(self):
  original=copy.deepcopy(RAW);plans=self.translated()
  self.assertEqual(RAW,original);self.assertEqual(len(plans),4)
  for raw,plan in zip(RAW['commands'],plans):
   expected=copy.deepcopy(raw['environment']);expected['LIGHTEFT_SOURCE_COMMIT']=pp.DRAFT_COMMIT;expected['LIGHTEFT_HARNESS_COMMIT']=self.commit
   self.assertEqual(plan['env'],expected);self.assertEqual(plan['argv'],raw['argv']);self.assertEqual(plan['cwd'],raw['cwd'])
   self.assertEqual(plan['sources'],[r['path'] for r in raw['submitted_sources']]);self.assertEqual(plan['source_bindings'],raw['submitted_sources'])
   self.assertEqual(plan['module'],c.TARGET);self.assertNotIn(pp.OLD_SOURCE_COMMIT,plan['env'].values())
   self.assertTrue(all('UNBOUND' not in v for v in plan['env'].values()))
  self.assertNotIn('MIMALLOC_VERBOSE',plans[2]['env']);self.assertEqual(plans[2]['env']['LEAN_NUM_THREADS'],'1')
  (self.root/'translated-plans.json').write_text(json.dumps(plans,indent=2)+'\n')
 def test_exact_command_binding_rejects_any_translated_field_mutation(self):
  spec=pp.normalize_plan(RAW);work=Path(spec['future_work_root']);plans=self.translated()
  inventory.exact_commands(spec,work,self.commit,plans)
  for change in ['argv','environment','search-path','source-commit','adapter-commit','sources','source-bindings','cwd','module']:
   bad=copy.deepcopy(plans)
   if change=='argv':bad[0]['argv'].append('--run')
   if change=='environment':bad[0]['env']['LANG']='C'
   if change=='search-path':bad[0]['env']['LEAN_PATH']=':'.join(bad[0]['env']['LEAN_PATH'].split(':')[:1]+bad[0]['env']['LEAN_PATH'].split(':')[2:])
   if change=='source-commit':bad[0]['env']['LIGHTEFT_SOURCE_COMMIT']='88d297fa58a15406aac6e7c0ea3c85f65965d19a'
   if change=='adapter-commit':bad[0]['env']['LIGHTEFT_HARNESS_COMMIT']='b'*40
   if change=='sources':bad[0]['sources']=[]
   if change=='source-bindings':bad[0]['source_bindings'][0]['sha256']='0'*64
   if change=='cwd':bad[0]['cwd']='/wrong'
   if change=='module':bad[0]['module']=pp.PROBABILITY_MODULE
   with self.subTest(change=change),self.assertRaisesRegex(c.Rejected,'Changed exact argv/environment'):inventory.exact_commands(spec,work,self.commit,bad)
 def test_placeholders_and_old_source_origin_cannot_activate(self):
  spec=pp.normalize_plan(RAW);work=Path(spec['future_work_root'])
  for commit in [pp.SOURCE_SLOT,pp.ADAPTER_SLOT,pp.OLD_SOURCE_COMMIT,pp.DRAFT_COMMIT,'2d75404bfd140d0e8ecb13d3c2554b853b9a1640','88d297fa58a15406aac6e7c0ea3c85f65965d19a','b6483cccabdf4afdbb8004a768afe8ea9ed0ff32','df18cdab7f15e5f377e6c72487e7beff6c5268e5']:
   with self.subTest(commit=commit),self.assertRaises(c.Rejected):pp.translate_commands(spec,work,commit)
  for source in [pp.SOURCE_SLOT,pp.OLD_SOURCE_COMMIT,'88d297fa58a15406aac6e7c0ea3c85f65965d19a','b'*40]:
   with self.subTest(source=source),self.assertRaisesRegex(c.Rejected,'draft source commit'):pp.translate_commands(spec,work,self.commit,source_commit=source)
 def test_wrong_source_schema_paths_or_roles_rejected(self):
  for change in ['path-list','swap','hash','cwd','extra-schema']:
   raw=copy.deepcopy(RAW)
   if change=='path-list':raw['commands'][0]['submitted_sources']=[raw['source']['path']]
   if change=='swap':raw['commands'][0]['submitted_sources']=[raw['audit']]
   if change=='hash':raw['commands'][0]['submitted_sources'][0]['sha256']='0'*64
   if change=='cwd':raw['commands'][0]['cwd']='/wrong'
   if change=='extra-schema':raw['commands'][0]['environment_additions']={}
   with self.subTest(change=change),self.assertRaises(c.Rejected):pp.normalize_plan(raw)
 def test_unexpected_environment_placeholder_and_old_slot_rejected(self):
  raw=copy.deepcopy(RAW);raw['commands'][0]['environment']['LIGHTEFT_SOURCE_COMMIT']=pp.OLD_SOURCE_COMMIT
  with self.assertRaisesRegex(c.Rejected,'slots differ'):pp.normalize_plan(raw)
  raw=copy.deepcopy(RAW);raw['commands'][0]['environment']['EXTRA']='UNBOUND_EXTRA'
  with self.assertRaisesRegex(c.Rejected,'Unresolved'):pp.translate_commands(pp.normalize_plan(raw),Path(raw['future_work_root']),self.commit)
 def test_wrong_target_counts_prefixes_and_options_rejected(self):
  for change in ['target','theorem','count','prefix','flags','sysroot']:
   raw=copy.deepcopy(RAW)
   if change=='target':raw['module']='LightEFTSuppliedForestStage.SuppliedForestGoodEvent'
   if change=='theorem':raw['theorem']='Wrong.theorem'
   if change=='count':raw['project_dependency_count']=196
   if change=='prefix':raw['project_namespace_prefixes']=raw['project_namespace_prefixes'][:-1]
   if change=='flags':raw['commands'][0]['argv'].append('--run')
   if change=='sysroot':raw['commands'][0]['environment']['LEAN_SYSROOT']='/wrong'
   with self.subTest(change=change),self.assertRaises(c.Rejected):pp.normalize_plan(raw)
 def test_exact_344_dependency_contract_and_345_import_scope(self):
  rows=[dict(r['object'],module=r['module']) for r in DEPS];scope.dependency_contract(rows)
  self.assertEqual(len(rows),344);self.assertEqual(len({r['module'] for r in rows}|{c.TARGET}),345)
  for bad in [rows[:-1],rows+[rows[0]]]:
   with self.assertRaisesRegex(c.Rejected,'344'):scope.dependency_contract(bad)
  for module in pp.ACCEPTED_OBJECTS:
   bad=copy.deepcopy(rows);next(r for r in bad if r['module']==module)['sha256']='0'*64
   with self.subTest(module=module),self.assertRaisesRegex(c.Rejected,'staged dependency'):scope.dependency_contract(bad)
 def test_actual_builder_uses_real_translation_with_synthetic_inventory(self):
  spec=pp.normalize_plan(RAW);deps={'bindings':[dict(r['object'],module=r['module']) for r in DEPS]}
  fake=types.SimpleNamespace(scan=lambda:{'semantic':{},'excluded':{},'old_semantic_count':1,'signature_count':0,'excluded_count':0})
  with (patch.object(driver,'reviewed_inputs',return_value=(spec,deps,{})),patch.object(driver,'reviewed_wrapper',return_value={}),
        patch.object(driver,'effective',return_value={'predicted':True}) as effective,
        patch.object(inventory,'load_inventory',return_value=(fake,{},{}))):
   bound=BUILD(Path(spec['future_work_root']),self.commit)
  self.assertEqual(bound['plans'],self.translated());self.assertEqual(len(bound['dependencies']),344)
  self.assertTrue(effective.call_args.kwargs['predicted']);self.assertFalse(Path(spec['future_work_root']).exists())
 def object_inventory(self,which=0):
  base=self.root/('objects-'+str(which));base.mkdir();oldroot=base/'old';oldroot.mkdir()
  acceptedroots=[base/'deterministic',base/'probability']
  for root in acceptedroots:root.mkdir()
  old=put(oldroot/'LightEFTSpanners/Existing.olean');prior={str(old):c.bind(old)}
  accepted=[put(root/Path(*module.split('.')).with_suffix('.olean'),('synthetic '+module).encode()) for root,module in zip(acceptedroots,pp.ACCEPTED_OBJECTS)]
  expected=[c.bind(path) for path in accepted];merged=copy.deepcopy(prior);immutable={}
  for row in expected:
   merged,one=inventory.add_immutable_accepted_object(merged,row);immutable.update(one)
  obj=inventory.Inventory(merged,[],{'exact_static_archives':sorted(inventory.ARCHIVES)},[],[oldroot,*acceptedroots],immutable=immutable)
  return obj,accepted[which],prior,expected[which]
 def test_accepted_supplement_keeps_old_bindings_and_admits_two_paths(self):
  obj,accepted,prior,expected=self.object_inventory();result=SCAN(obj)
  for path,row in prior.items():self.assertEqual(obj.prior[path],row)
  self.assertEqual(set(result['semantic']),set(prior)|set(obj.immutable));self.assertEqual(result['accepted_object_count'],2)
  put(accepted.parent/'Extra.olean')
  with self.assertRaisesRegex(c.Rejected,'Unknown search input'):SCAN(obj)
 def test_each_accepted_object_content_mutation_rejected(self):
  for which in range(2):
   with self.subTest(which=which):
    obj,accepted,_,_=self.object_inventory(which);accepted.write_bytes(b'mutated')
    with self.assertRaisesRegex(c.Rejected,'hash drift'):SCAN(obj)
 def test_each_equal_bytes_replacement_identity_rejected(self):
  for which in range(2):
   with self.subTest(which=which):
    obj,accepted,_,_=self.object_inventory(which);replacement=put(self.root/('replacement-'+str(which)),accepted.read_bytes());os.replace(replacement,accepted)
    with self.assertRaisesRegex(c.Rejected,'Accepted object identity/content mutation'):SCAN(obj)
 def test_each_accepted_supplement_cannot_override_old_hash(self):
  for which in range(2):
   with self.subTest(which=which):
    obj,accepted,prior,expected=self.object_inventory(which);prior[str(accepted)]=dict(expected,sha256='0'*64)
    with self.assertRaisesRegex(c.Rejected,'cannot replace'):inventory.add_immutable_accepted_object(prior,expected)
 def test_production_supplements_pin_both_module_path_bytes_identity(self):
  spec=pp.normalize_plan(RAW);policy=json.loads((HERE/'accepted-object-supplement.json').read_text())
  expected={RAW[key]['object']['path']:RAW[key]['object'] for key,_,_,_ in pp.ACCEPTED_OBJECTS.values()}
  self.assertEqual(pp.accepted_supplements(policy,spec),expected)
  for index in range(2):
   for change in ['module','path','hash','bytes','identity','evidence']:
    bad=copy.deepcopy(policy);row=bad['objects'][index]
    if change=='module':row['module']='Other.Module'
    if change=='path':row['object']['path']='/wrong/object.olean'
    if change=='hash':row['object']['sha256']='0'*64
    if change=='bytes':row['object']['bytes']+=1
    if change=='identity':row['object']['identity'][1]+=1
    if change=='evidence':row['accepted_evidence_commit']='0'*40
    with self.subTest(index=index,change=change),self.assertRaises(c.Rejected):pp.accepted_supplements(bad,spec)
  for change in ['missing','duplicate','extra','draft']:
   bad=copy.deepcopy(policy)
   if change=='missing':bad['objects'].pop()
   if change=='duplicate':bad['objects'][1]=bad['objects'][0]
   if change=='extra':bad['objects'].append(bad['objects'][0])
   if change=='draft':bad['reviewed_draft_commit']='88d297fa58a15406aac6e7c0ea3c85f65965d19a'
   with self.subTest(change=change),self.assertRaises(c.Rejected):pp.accepted_supplements(bad,spec)
 def test_masking_duplicates_and_wrong_root_sidecars_still_fail(self):
  fresh=self.root/'fresh';fresh.mkdir();old=self.root/'old';old.mkdir()
  previousroots=[self.root/'deterministic',self.root/'probability']
  for root in previousroots:root.mkdir()
  dep=put(old/'LightEFTSpanners/Existing.olean')
  previous={module:c.bind(put(root/Path(*module.split('.')).with_suffix('.olean'))) for root,module in zip(previousroots,pp.ACCEPTED_OBJECTS)}
  target=fresh/Path(*c.TARGET.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True)
  expected={'LightEFTSpanners.Existing':c.bind(dep),**previous};roots=[fresh,*reversed(previousroots),old]
  c.effective(roots,expected,target,False)
  for module in pp.ACCEPTED_OBJECTS:
   mask=fresh/module.split('.')[0];mask.mkdir()
   with self.assertRaisesRegex(c.Rejected,'Package selection masks'):c.effective(roots,expected,target,False)
   mask.rmdir();marker=put(fresh/(module.split('.')[0]+'.olean'))
   with self.assertRaisesRegex(c.Rejected,'Package selection masks'):c.effective(roots,expected,target,False)
   marker.unlink()
  for module in ['LightEFTSpanners.Existing',*pp.ACCEPTED_OBJECTS]:
   duplicate=put(fresh/Path(*module.split('.')).with_suffix('.olean'))
   with self.assertRaisesRegex(c.Rejected,'Shadow/missing/wrong'):c.effective(roots,expected,target,False)
   duplicate.unlink();duplicate.parent.rmdir()
  put(target);put(old/Path(*c.TARGET.split('.')).with_suffix('.ir.sig'))
  with self.assertRaisesRegex(c.Rejected,'Target sidecar shadow'):c.effective(roots,expected,target,True)
 def context_fixture(self,wrong_binding=False):
  root=self.root/('bad' if wrong_binding else 'good');root.mkdir()
  work=root/'work';work.mkdir();objects=work/'objects';objects.mkdir();old=root/'old';old.mkdir();evidence=root/'evidence';evidence.mkdir()
  dep=put(old/'LightEFTSpanners/Existing.olean');source=put(root/'source.lean.txt',b'synthetic source; never sent to Lean')
  sb=c.bind(source);expected=copy.deepcopy(sb)
  if wrong_binding:expected['sha256']='0'*64
  plan={'stage':'compile','module':c.TARGET,'argv':[sys.executable],'env':{'LEAN_PATH':str(objects)+':'+str(old)},'sources':[str(source)],'source_bindings':[expected],'cwd':str(work)}
  fake=types.SimpleNamespace(file=None,acquired_ns=0,check=lambda:None)
  ctx=scope.Context(work,evidence,fake,[plan],[objects,old],{'LightEFTSpanners.Existing':c.bind(dep)},{str(dep):c.bind(dep),str(source):sb},fixture=True)
  ctx.target.parent.mkdir(parents=True);(evidence/'compile').mkdir()
  return ctx,plan
 def test_context_records_exact_translated_source_and_cwd(self):
  ctx,plan=self.context_fixture();record={};ctx.before_child(plan,record,lambda:None)
  self.assertEqual(record['working_directory'],plan['cwd']);self.assertEqual(record['planned_source_bindings'],plan['source_bindings'])
  self.assertEqual(record['submitted_sources'][0]['sha256'],plan['source_bindings'][0]['sha256'])
  bad,p=self.context_fixture(wrong_binding=True)
  with self.assertRaisesRegex(c.Rejected,'Translated submitted source binding'):bad.before_child(p,{},lambda:None)
 def audit_fixture(self,omit=None):
  ci=self.root/('ci-'+str(omit));ci.mkdir();names=[r['module'] for r in DEPS];loaded=sorted(names+[c.TARGET])
  put(ci/'import-closure-loaded.txt',('\n'.join(loaded)+'\n').encode());put(ci/'strict-violations.txt',b'\n')
  put(ci/'actual-owner-inventory.tsv',f'owner\tname\tkind\tunsafe\tpartial\n{c.TARGET}\t{c.THEOREM}\ttheorem\tfalse\tfalse\n'.encode())
  interfaces=[n for n in pp.REQUIRED_INTERFACES if n!=omit]
  owners=dict(zip(pp.REQUIRED_INTERFACES,['LightEFTSpanners.StoredForestOutputLaw',pp.PROBABILITY_MODULE,pp.ACCEPTED_MODULE,'LightEFTSpanners.ComputableVotingSamples','LightEFTSpanners.FiniteLaw']))
  rows=[f'{c.THEOREM}\t{c.TARGET}\ttheorem\t\t'+','.join(interfaces)+'\tfalse\tfalse\n']
  rows += [f'{name}\t{owners[name]}\ttheorem\t\tpropext\tfalse\tfalse\n' for name in interfaces]
  rows += ['propext\t[anonymous]\taxiom\t\t\tfalse\tfalse\n']
  put(ci/'recursive-dependencies.tsv',('name\towner\tkind\ttypeDependencies\tbodyDependencies\tunsafe\tpartial\n'+''.join(rows)).encode())
  raw=f'PASS: 1 new-module actual-owner declarations; {len(rows)} recursive constants, 0 opaque bodies; axioms [propext]\n'
  return ci,names,raw
 def test_audit_all_five_prefixes_and_derived_counts(self):
  ci,names,raw=self.audit_fixture();result=audit.validate(ci,names,raw)
  self.assertEqual(result['recursive_constants'],len(pp.REQUIRED_INTERFACES)+2);self.assertEqual(result['new_owner_roots'],1)
  self.assertEqual(len(result['project_imports']),345)
  self.assertTrue(all(c.project(prefix+'.Example') for prefix in pp.PREFIXES))
 def test_audit_rejects_each_missing_interface_independently(self):
  for i,name in enumerate(pp.REQUIRED_INTERFACES):
   with self.subTest(interface=name):
    ci,names,raw=self.audit_fixture(omit=name)
    # Every remaining serialized row is reachable and the fabricated PASS
    # counts agree. Only the independent mandatory-interface check rejects it.
    with self.assertRaisesRegex(c.Rejected,'Missing required reachable interface: '+name.replace('.','\\.')):audit.validate(ci,names,raw)
 def test_audit_rejects_missing_or_extra_stage_prefix(self):
  ci,names,raw=self.audit_fixture();p=ci/'import-closure-loaded.txt';original=p.read_text()
  for bad in [original.replace(module+'\n','') for module in [pp.ACCEPTED_MODULE,pp.PROBABILITY_MODULE,c.TARGET]]+[original+prefix+'.Unexpected\n' for prefix in pp.PREFIXES]:
   p.write_text(bad)
   with self.assertRaisesRegex(c.Rejected,'Exact project imports differ'):audit.validate(ci,names,raw)
 def test_latest_released_receipt_full_epoch_and_hash(self):
  known=authority.known_released_lock()
  self.assertEqual(known['released_epoch'],'f8ff4af575274e8c9aec76c264ef7726')
  self.assertEqual(known['receipt']['sha256'],'f1cb1eb90fcaa82f55c84d2be396f561794e6b83096a9e3970e3424d0f9cf6ef')
  self.assertEqual((known['identity']['device'],known['identity']['inode']),(33,3258))
  data=(pp.ROOT/known['receipt']['path']).read_bytes();self.assertEqual(len(data),718)
  self.assertEqual(c.sha(data),known['receipt']['sha256']);self.assertEqual(known['receipt']['commit'],'df18cdab7f15e5f377e6c72487e7beff6c5268e5')
  body=json.loads(data);self.assertEqual(body['state'],'released');self.assertTrue(body['kernel_echild']);self.assertEqual(body['epoch'],known['released_epoch'])
 def document(self):
  return dict(approved_wrapper_commit=self.commit,exclusive_worker=True,reviewer_idle=True,allow_new_epoch=True,
   same_directory='/tmp',coordination_reference='synthetic authority only',facts={'synthetic':'owner'},issued_ns=10,
   allow_released_lock_reuse=True,released_lock_identity=copy.deepcopy(authority.known_released_lock()['identity']))
 def test_conflicting_or_missing_coordination_rejected(self):
  original=self.document();authority.check_document(original,self.commit,current=original['facts'],now=11)
  for change in ['commit','worker','reviewer','epoch-authority','directory','reference','owner','reuse','inode','future','stale']:
   doc=copy.deepcopy(original)
   if change=='commit':doc['approved_wrapper_commit']=pp.DRAFT_COMMIT
   if change=='worker':doc['exclusive_worker']=False
   if change=='reviewer':doc['reviewer_idle']=False
   if change=='epoch-authority':doc['allow_new_epoch']=False
   if change=='directory':doc['same_directory']='/wrong'
   if change=='reference':doc['coordination_reference']=''
   if change=='owner':doc['facts']={'synthetic':'competing owner'}
   if change=='reuse':doc['allow_released_lock_reuse']=False
   if change=='inode':doc['released_lock_identity']['inode']+=1
   if change=='future':doc['issued_ns']=12
   now=10+60*10**9 if change=='stale' else 11
   with self.subTest(change=change),self.assertRaises(c.Rejected):authority.check_document(doc,self.commit,current=original['facts'],now=now)
 def test_authority_rejects_conflicting_release_epoch_hash_and_blob(self):
  known=authority.known_released_lock();receipt=(pp.ROOT/known['receipt']['path']).read_bytes();doc=self.document()
  for change in ['valid','epoch','hash','blob']:
   policy=copy.deepcopy(known);blob=receipt
   if change=='epoch':policy['released_epoch']='7d164441f8ac44d9b9c316cdd79869f3'
   if change=='hash':policy['receipt']['sha256']='0'*64
   if change=='blob':blob=receipt+b'\n'
   with (self.subTest(change=change),patch.object(authority,'known_released_lock',return_value=policy),
    patch.object(scope,'reviewed_wrapper',return_value={}),patch.object(authority,'facts',return_value=doc['facts']),
    patch.object(authority.time,'monotonic_ns',return_value=11),patch.object(authority.subprocess,'check_output',return_value=blob)):
    if change=='valid':self.assertEqual(authority.ReviewedAuthority(self.commit,doc).released_lock,known)
    else:
     with self.assertRaisesRegex(c.Rejected,'receipt differs|epoch differs'):authority.ReviewedAuthority(self.commit,doc)
 def test_preissued_or_absent_activation_authority_rejected(self):
  for kwargs in [{},{'reviewed_commit':self.commit,'coordination':self.document()},
   {'reviewed_commit':self.commit,'coordination':lambda:self.document(),'automatic_retry':True}]:
   with self.subTest(kwargs=list(kwargs)),self.assertRaises(c.ProductionDisabled):driver.execute_production(**kwargs)
 def test_signature_metadata_classification_and_old_hashes_preserved(self):
  root=self.root/'library';root.mkdir();olean=put(root/'Fixture/Existing.olean');ir=put(root/'Fixture/Existing.ir');sig=put(root/'Fixture/Existing.ir.sig')
  oldmetadata=put(root/'Fixture/Existing.olean.hash',b'bound old metadata');prior={str(p):c.bind(p) for p in [olean,ir,oldmetadata]}
  signature=c.bind(sig);signature.update(module='Fixture.Existing',family={'olean':{'path':str(olean),'sha256':prior[str(olean)]['sha256']},'ir':{'path':str(ir),'sha256':prior[str(ir)]['sha256']}},qualification=inventory.QUALIFICATION)
  forms=('.ilean.hash','.olean.hash','.olean.server.hash','.olean.private.hash','.ir.sig.hash','.ir.hash','.trace')
  self.assertEqual(inventory.METADATA_FORMS,forms);self.assertEqual(len(inventory.ARCHIVES),10)
  diagnosis=[]
  for suffix in forms:
   path=root/('Fixture/Existing'+suffix)
   if not path.exists():put(path,b'excluded metadata only')
   diagnosis.append({'path':str(path)})
  policy={'exact_static_archives':sorted(inventory.ARCHIVES)}
  obj=inventory.Inventory(prior,[signature],policy,diagnosis,[root]);excluded=set(obj.excluded)
  def metadata_never_hashed(path,expected=None):
   self.assertNotIn(str(path),excluded);return c.bind(path,expected)
  with patch.object(inventory,'bind',side_effect=metadata_never_hashed):result=SCAN(obj)
  self.assertEqual(result['old_semantic_count'],3);self.assertEqual(result['signature_count'],1)
  self.assertEqual(result['excluded_count'],6);self.assertIn(str(oldmetadata),result['semantic'])
  for path,row in prior.items():self.assertEqual(obj.prior[path],row)
  bad=copy.deepcopy(signature);bad['family']['ir']['sha256']='0'*64
  with self.assertRaisesRegex(c.Rejected,'family association'):inventory.Inventory(prior,[bad],policy,diagnosis,[root])
  bad=copy.deepcopy(signature);bad['qualification']='unqualified'
  with self.assertRaisesRegex(c.Rejected,'qualification'):inventory.Inventory(prior,[bad],policy,diagnosis,[root])
  olean.write_bytes(b'changed old object')
  with self.assertRaisesRegex(c.Rejected,'hash drift'):SCAN(obj)
 def test_unknown_accepted_root_signature_sidecar_and_link_rejected(self):
  obj,accepted,_,_=self.object_inventory();extra=put(accepted.with_suffix('.ir.sig'))
  with self.assertRaisesRegex(c.Rejected,'New/unreviewed signature'):SCAN(obj)
  extra.unlink();extra=put(accepted.with_suffix('.trace'))
  with self.assertRaisesRegex(c.Rejected,'Unknown search input'):SCAN(obj)
  extra.unlink();link=accepted.parent/'linked.olean';os.link(accepted,link)
  with self.assertRaisesRegex(c.Rejected,'linked search input'):SCAN(obj)
  link.unlink();link.symlink_to(accepted)
  with self.assertRaisesRegex(c.Rejected,'Nonregular/linked'):SCAN(obj)
 def test_audit_count_warning_axiom_and_ownership_boundaries(self):
  ci,names,raw=self.audit_fixture();audit.validate(ci,names,raw)
  for bad in [raw.replace('7 recursive','8 recursive'),raw+'warning: fixture diagnostic\n',raw+raw]:
   with self.subTest(raw=bad),self.assertRaises(c.Rejected):audit.validate(ci,names,bad)
  dep=ci/'recursive-dependencies.tsv';original=dep.read_text()
  for bad in [original.replace('propext','ForbiddenAxiom'),original.replace('\tfalse\tfalse','\ttrue\tfalse'),
   original.replace(pp.PROBABILITY_MODULE, c.TARGET)]:
   dep.write_text(bad)
   with self.subTest(change=bad[-100:]),self.assertRaises(c.Rejected):audit.validate(ci,names,raw)
  dep.write_text(original)
 def test_first_failure_stops_before_other_stages(self):
  work=self.root/'work';evidence=self.root/'evidence';evidence.mkdir();plans=self.translated()
  for plan in plans:plan['cwd']=str(work/'audit' if plan['stage']=='audit' else work)
  fake=types.SimpleNamespace(target=work/'objects/Fixture/Target.olean',preservation_failed=False,
   finish=lambda:forbidden())
  class FakeLease:
   record={'state':'released','kernel_echild':True}
   def __enter__(self):return self
   def __exit__(self,*args):return False
  with (patch.object(driver,'Context',return_value=fake),patch.object(driver.child_runner,'run_child',side_effect=c.Rejected('synthetic first failure')) as run,
   patch.object(driver,'verify_receipts',side_effect=forbidden)):
   result=driver._run_batch(work,evidence,plans,[],{}, {},FakeLease(),True,self.commit)
  self.assertFalse(result['accepted']);self.assertIn('synthetic first failure',result['failure']);self.assertEqual(run.call_count,1);self.assertEqual(result['stages'],[])
 def test_stale_authority_stops_before_claim_work_evidence_or_lock(self):
  clock=[1];facts={'synthetic':'owner only'};work=self.root/'work';evidence=self.root/'evidence';state={'provider':0};bound={'inputs':{},'roots':[work/'objects']}
  known=authority.known_released_lock();receipt=(pp.ROOT/known['receipt']['path']).read_bytes()
  def planning(*args):clock[0]+=96*10**9;return bound
  def provider():
   state['provider']+=1;issued=clock[0];clock[0]+=60*10**9
   return dict(approved_wrapper_commit=self.commit,exclusive_worker=True,reviewer_idle=True,allow_new_epoch=True,same_directory='/tmp',coordination_reference='synthetic stale authority only',facts=facts,issued_ns=issued,allow_released_lock_reuse=True,released_lock_identity=known['identity'])
  with (patch.object(driver,'HERE',self.root),patch.object(driver,'reviewed_inputs',return_value=({'future_work_root':str(work),'future_evidence_root':str(evidence)},None,None)),
        patch.object(driver,'make_production_plan',planning),patch.object(scope,'reviewed_wrapper',return_value={}),patch.object(authority,'facts',return_value=facts),
        patch.object(authority.time,'monotonic_ns',side_effect=lambda:clock[0]),patch.object(authority.subprocess,'check_output',return_value=receipt)):
   with self.assertRaisesRegex(c.Rejected,'Stale/future'):driver.execute_production(self.commit,provider)
  self.assertEqual(state['provider'],1);self.assertFalse(work.exists());self.assertFalse(evidence.exists());self.assertFalse((self.root/'production-invocation-claimed.json').exists())

if __name__=='__main__':
 def guard(event,args):
  if event=='open' and isinstance(args[0],(str,bytes,os.PathLike)):
   path=str(Path(os.fsdecode(args[0])).absolute())
   if path=='/tmp/distance-sparsification-single-compiler.lock' or path.startswith(('/proc/','/sys/')):raise AssertionError('No common lock or resource/ownership probes in preparation fixtures')
 sys.addaudithook(guard)
 with contextlib.ExitStack() as stack:
  for obj,name in [(driver,'make_production_plan'),(inventory.Inventory,'scan'),(driver.subprocess,'Popen'),(driver.child_runner,'run_child'),(driver.child_runner,'VisibleAccounting'),
    (lease.Lease,'__enter__'),(fcntl,'flock'),(os,'fork'),(os,'statvfs'),(shutil,'disk_usage'),(resource,'getrlimit'),(resource,'setrlimit'),(resource,'getrusage')]:stack.enter_context(patch.object(obj,name,forbidden))
  result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Adapter))
 c.save(RUN/'result.json',dict(tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),successful=result.wasSuccessful(),events=EVENTS,
  qualification='Synthetic Python fixtures and real reviewed-plan JSON translation only; no Lean, real inventory, production, common-lock acquisition or resource probes'))
 print('ADAPTER_FIXTURE_EVIDENCE='+str(RUN))
 sys.exit(0 if result.wasSuccessful() else 1)
