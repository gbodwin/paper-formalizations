"""Source/object reconciliation and an unexecuted plan only; no Lean or lock API."""
from pathlib import Path
import collections,copy,hashlib,json,os,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
PREVIOUS=ROOT/'checkpoints/light-eft-actual-supplied-forest-probability-draft-20261018'
RUNTIME=PREVIOUS/'future-validation-evidence'
ADAPTER=ROOT/'checkpoints/light-eft-actual-supplied-forest-probability-adapter-20261018'
ACCEPTED='49f17551c0c092c9631f36e2108114cc83c8eebe'
FROZEN='78cb40c7837db049d645d73696f2e0b724ce8a3b'
MODULE='LightEFTJointFlagSamplingStage.JointAssignmentLaw'
THEOREM='LightEFTSpanners.JointFlagSampling.decoded_assignment_probability'
REQUIRED=[
 'LightEFTSpanners.StoredFlagBatch.original_probability',
 'LightEFTSpanners.StoredFlagSample.typed_edgeSet',
 'LightEFTSpanners.FiniteProbability.productLaw',
 'LightEFTSpanners.FiniteProbability.productLaw_measure',
 'LightEFTSpanners.FiniteProbability.Law.prob_map',
 'LightEFTSpanners.FiniteProbability.Law.prob_bind',
 'LightEFTSpanners.SampledGreedy.freshBatchLaw',
 'LightEFTSpanners.SampledGreedy.executionLaw']
ROOT_THEOREMS=['Transport.mass_ext','Transport.eq_of_prob_eq','Transport.product_map',
 'Transport.batch_eq_product','Transport.fin_cons_probability','samplingSchedule_nodup',
 'mem_samplingSchedule','samplingSchedule_length','jointSourceLaw_mass','decodeHost_typed',
 'decodeAssignment_head','decodeAssignment_outside','batch_decode_law','host_decode_law',
 'decoded_assignment_probability','decoded_assignment_law']

def guard(event,args):
 if event=='subprocess.Popen':assert args[0]=='git' and args[1][0]=='git' and args[1][1]=='show','Only local Git blob reads'
 if event in ['fcntl.flock','os.fork','os.posix_spawn']:raise AssertionError('No execution/lock activation')
 if event=='open' and isinstance(args[0],(str,bytes,os.PathLike)):
  p=os.path.abspath(os.fsdecode(args[0]));assert p!='/tmp/distance-sparsification-single-compiler.lock' and not p.startswith(('/proc/','/sys/')),'No common-lock/resource/ownership probes'
sys.addaudithook(guard)
def sha(b):return hashlib.sha256(b).hexdigest()
def bind(path,expected=None):
 p=Path(path);assert p.is_absolute() and p.is_file() and not p.is_symlink(),str(p)
 for parent in p.parents:assert not parent.is_symlink()
 a=p.stat();assert a.st_nlink==1;b=p.read_bytes();z=p.stat()
 identity=lambda s:[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
 assert identity(a)==identity(z)
 row=dict(path=str(p),bytes=len(b),sha256=sha(b),identity=identity(z))
 if expected:
  for key in ['bytes','sha256','identity']:
   if key in expected:assert row[key]==expected[key],str(p)+' '+key
 return row
def load(p):return json.loads(Path(p).read_bytes())
def write(name,obj):(HERE/name).write_text(json.dumps(obj,indent=2)+'\n')
def git_bound(path,commit):
 b=subprocess.check_output(['git','show',commit+':'+str(path.relative_to(ROOT))],cwd=ROOT)
 assert path.read_bytes()==b,str(path);return bind(path)
def imports(path):return [line.split()[1] for line in path.read_text().splitlines() if line.startswith('import ')]

def main():
 oldplan=load(PREVIOUS/'focused-validation-plan.json')
 git_bound(PREVIOUS/'project-dependency-bindings.json','cde705e91972f00497cfd5fe1235f0eeb2448904')
 oldclosure=load(PREVIOUS/'project-dependency-bindings.json')
 graphpath=ROOT/'checkpoints/light-eft-clean-context-preparation-20261018/frozen-graph.json'
 graph=bind(graphpath,oldclosure['frozen_source_graph']);git_bound(graphpath,ACCEPTED)
 nodes={x['module']:x for x in load(graphpath)}
 result=load(RUNTIME/'result.json');assert result['accepted'] and result['result']['preserved']
 journal_binding=bind(RUNTIME/'inputs.jsonl',result['result']['input_export']);git_bound(RUNTIME/'inputs.jsonl',ACCEPTED)
 journal={row['path']:row for row in map(json.loads,(RUNTIME/'inputs.jsonl').read_text().splitlines())}
 source=HERE/'staged/LightEFTJointFlagSamplingStage/JointAssignmentLaw.lean'
 assert not re.search(rb'\b(sorry|admit|axiom|unsafe|partial)\b',source.read_bytes())
 direct=imports(source);seeds=[n for n in direct if n.startswith(('LightEFTSpanners.','LightSpanners.'))]
 todo=seeds.copy();seen=set()
 while todo:
  name=todo.pop()
  if name in seen:continue
  seen.add(name);assert name in nodes;todo.extend(nodes[name]['project_imports'])
 assert len(seen)==77
 oldroots=oldplan['commands'][0]['environment']['LEAN_PATH'].split(':');objroot=Path(oldroots[3]);rows=[]
 for name in sorted(seen):
  node=nodes[name];src=bind(ROOT/node['path'],node);obj=objroot/Path(*name.split('.')).with_suffix('.olean')
  assert str(obj) in journal,'Missing old protected object: '+name
  rows.append(dict(module=name,source_commit=FROZEN,source=src,object=bind(obj,journal[str(obj)]),
   prior_protected_object=journal[str(obj)],direct_project_imports=node['project_imports']))
 write('project-dependency-bindings.json',dict(status='Source/import and existing protected object-byte reconciliation only',
  direct_imports=seeds,dependencies=rows,total_project_dependencies=77,expected_project_imports_including_target=78,
  namespace_counts=dict(collections.Counter(x['module'].split('.')[0] for x in rows)),frozen_source_graph=graph,
  inherited_protected_journal=journal_binding,accepted_staged_modules_imported=0))
 jsonl=HERE/'project-dependency-bindings.jsonl';jsonl.write_text(''.join(json.dumps(x,separators=(',',':'))+'\n' for x in rows))
 directory=HERE/'project-closure-export';directory.mkdir(exist_ok=False);parts=[];buffer=bytearray()
 def flush():
  if not buffer:return
  data=bytes(buffer);p=directory/('part-%04d.txt'%len(parts));p.write_bytes(data)
  parts.append(dict(path=p.name,bytes=len(data),sha256=sha(data)));buffer.clear()
 for line in jsonl.read_bytes().splitlines(keepends=True):
  if buffer and len(buffer)+len(line)>200000:flush()
  buffer.extend(line)
 flush();assert b''.join((directory/x['path']).read_bytes() for x in parts)==jsonl.read_bytes()
 (directory/'manifest.json').write_text(json.dumps(dict(source=str(jsonl),bytes=jsonl.stat().st_size,sha256=sha(jsonl.read_bytes()),row_aligned=True,target_bytes=200000,parts=parts),indent=2)+'\n')
 # Preserve all three accepted staged outputs without importing or replaying them.
 accepted=[]
 for key in ['accepted_deterministic_dependency','accepted_probability_dependency']:
  row=oldplan[key];accepted.append(dict(module=row['module'],source_commit=row['source_commit'],
   accepted_evidence_commit=row['accepted_evidence_commit'],source=bind(row['source']['path'],row['source']),object=bind(row['object']['path'],row['object'])))
 actual=load(RUNTIME/'compile/receipt.json')['outputs_after']['new_objects'][0]
 assert actual['bytes']==145656 and actual['sha256']=='000a803f858c98d95c53b57011785f5c08fc687ee5af081161b595bd32974499'
 accepted.append(dict(module=oldplan['module'],source_commit='cde705e91972f00497cfd5fe1235f0eeb2448904',accepted_evidence_commit=ACCEPTED,
  source=bind(oldplan['source']['path'],oldplan['source']),object=bind(actual['path'],actual)))
 write('accepted-preservation-bindings.json',dict(objects=accepted,imported_as_dependencies=False,recompiled=False,
  qualification='User-reported qualified incremental acceptance recorded as source/log/hash reconciliation only; no fresh execution.'))
 # Bind the explicitly imported and inspected pinned-mathlib interfaces.
 mathlib=Path('/workspace/paper-formalizations/.lake/packages/mathlib');mathroot=Path(oldroots[4]);mathnames=[n for n in direct if n.startswith('Mathlib.')]
 mathnames+=['Mathlib.Algebra.BigOperators.Ring.Finset','Mathlib.Algebra.BigOperators.GroupWithZero.Finset','Mathlib.Data.Fintype.BigOperators']
 mathrows=[]
 for name in sorted(set(mathnames)):
  src=mathlib/Path(*name.split('.')).with_suffix('.lean');obj=mathroot/Path(*name.split('.')).with_suffix('.olean')
  assert str(obj) in journal,'Missing bound mathlib interface: '+name
  mathrows.append(dict(module=name,direct_import=name in direct,source=bind(src),object=bind(obj,journal[str(obj)]),prior_protected_object=journal[str(obj)]))
 write('mathlib-interface-bindings.json',dict(qualification='Pinned dependency sources and prior-bound local objects; no authenticated provenance or fresh execution',interfaces=mathrows))
 pins=[]
 for name in ['lean-toolchain','lake-manifest.json']:pins.append(git_bound(ROOT/name,FROZEN))
 interface_names=['LightEFTSpanners.StoredFlagBatchProbability','LightEFTSpanners.StoredFlagSampleProbability',
  'LightEFTSpanners.StoredFlagSampleEncoding','LightEFTSpanners.BernoulliFlagEncoding','LightEFTSpanners.FiniteProductLaw',
  'LightEFTSpanners.FiniteLaw','LightEFTSpanners.ProductSampleConcentration','LightEFTSpanners.BernoulliTestConcentration',
  'LightEFTSpanners.FreshVotingTapes','LightEFTSpanners.AdaptiveVotingConcentration']
 byname={x['module']:x for x in rows};write('interface-bindings.json',[byname[x] for x in interface_names])
 (HERE/'interface-declarations.txt').write_text('\n\n'.join('MODULE '+name+'\nSOURCE '+byname[name]['source']['path']+'\n'+Path(byname[name]['source']['path']).read_text() for name in interface_names))
 audit=(PREVIOUS/'staged/PolynomialActualSuppliedForestProbabilityAudit.lean').read_text().replace(oldplan['module'],MODULE).replace(oldplan['theorem'],THEOREM)
 audit='\n'.join(('  let required : Array Name := #['+', '.join('"'+n+'".toName' for n in REQUIRED)+']') if line.startswith('  let required : Array Name := #[') else line for line in audit.splitlines())+'\n'
 anchor='  let kind := fun c => match c with'
 extra='  let requiredRoots : Array Name := #['+', '.join('"LightEFTSpanners.JointFlagSampling.'+n+'".toName' for n in ROOT_THEOREMS)+']\n  for n in requiredRoots do\n    unless roots.contains n do throwError "Missing joint-law root {n}"\n'
 assert anchor in audit;audit=audit.replace(anchor,extra+anchor).replace('Missing actual supplied-forest probability theorem','Missing joint assignment probability theorem')
 auditpath=HERE/'staged/JointAssignmentLawAudit.lean';auditpath.write_text(audit)
 resolverpath=HERE/'staged/ResolveJointAssignmentLawTarget.lean';resolverpath.write_text((PREVIOUS/'staged/ResolvePolynomialActualSuppliedForestTarget.lean').read_text().replace(oldplan['module'],MODULE))
 bindings=dict(source=bind(source),audit=bind(auditpath),resolver=bind(resolverpath))
 work=ROOT/'.lake/joint-flag-assignment-76a78fe87ed74ab395396879287c05bb';evidence=HERE/'future-validation-evidence';assert not work.exists() and not evidence.exists()
 objects=work/'objects';target=objects/Path(*MODULE.split('.')).with_suffix('.olean');roots=[objects]+list(map(Path,oldroots[3:]))
 sys.path.insert(0,str(ADAPTER));from package_selection import selected_path
 predicted=[]
 for row in rows:
  selected=selected_path(roots,row['module'],predicted_dirs=[objects/MODULE.split('.')[0]],predicted_files=[target]);assert str(selected)==row['object']['path']
  predicted.append(dict(module=row['module'],selected=str(selected),expected=row['object']['path']))
 assert selected_path(roots,MODULE,predicted_dirs=[objects/MODULE.split('.')[0]],predicted_files=[target])==target
 write('package-layout-prediction.json',dict(status='Metadata-only prediction; no output directory created',roots=list(map(str,roots)),dependencies=predicted,
  new_module=MODULE,predicted_new_object=str(target),dependency_selection_matches=77,accepted_staged_objects_not_in_search_path=True))
 release_binding=git_bound(RUNTIME/'lease.json',ACCEPTED);assert release_binding['bytes']==719 and release_binding['sha256']=='26141424860045dba7f6e2438abcf5615cef11b29b27b242ec24de5a9dc6e504'
 release=load(RUNTIME/'lease.json');assert release['state']=='released' and release['kernel_echild'] and release['epoch']=='f9446665c62e4e5c90b1578b930dd6ec'
 plan=copy.deepcopy(oldplan)
 for key in ['accepted_probability_dependency','accepted_deterministic_dependency']:plan.pop(key)
 plan.update(status='DRAFT_PLAN_ONLY; no executable adapter or execution authority',module=MODULE,theorem=THEOREM,**bindings,
  new_object=str(target),new_object_hash=None,future_work_root=str(work),future_evidence_root=str(evidence),work_and_evidence_created=False,
  accepted_staged_preservation=bind(HERE/'accepted-preservation-bindings.json'),accepted_staged_objects_imported=0,
  project_closure=bind(HERE/'project-dependency-bindings.json'),project_dependency_count=77,expected_project_module_import_count_including_new_target=78,
  project_namespace_prefixes=['LightEFTSpanners','LightSpanners','LightEFTJointFlagSamplingStage'],mathlib_interface_bindings=bind(HERE/'mathlib-interface-bindings.json'),pins=pins)
 env=copy.deepcopy(oldplan['commands'][0]['environment']);env['LEAN_PATH']=':'.join(map(str,roots))
 env['LEAN_SRC_PATH']=':'.join([str(HERE/'staged')]+oldplan['commands'][0]['environment']['LEAN_SRC_PATH'].split(':')[3:])
 lean=oldplan['commands'][0]['argv'][0];checker=oldplan['commands'][2]['argv'][0];flags=oldplan['commands'][0]['argv'][1:6]
 argvs=[[lean]+flags+['--root='+str(HERE/'staged'),'-o',str(target),str(source)],[lean]+flags+[str(resolverpath)],[checker,'-v',MODULE],[lean]+flags+[str(auditpath)]]
 roles=[['source'],['resolver','source'],['source'],['audit','source']];plan['commands']=[]
 for i,stage in enumerate(['compile','resolve','replay','audit']):
  stageenv=copy.deepcopy(env)
  if stage=='resolve':stageenv.update(LIGHTEFT_CHECKER_TARGET=MODULE,LIGHTEFT_CHECKER_RESOLUTION_FILE=str(work/'resolution.json'))
  if stage=='replay':stageenv.pop('MIMALLOC_VERBOSE');stageenv.update(LEAN_NUM_THREADS='1',LEAN_STACK_SIZE_KB='65536')
  length=len(json.dumps(dict(argv=argvs[i],env=stageenv,stage=stage)).encode());assert length<=4096
  plan['commands'].append(dict(stage=stage,argv=argvs[i],environment=stageenv,submitted_sources=[bindings[k] for k in roles[i]],cwd=str(work/'audit' if stage=='audit' else work),
   visible_admission_bytes=oldplan['commands'][i]['visible_admission_bytes'],executed=False,launcher_config_bytes_with_placeholders=length))
 plan['interface_review']='Review generic finite-law transport proofs, full product mass, occurrence-indexed/tail-first decoder and arbitrary-event equality. No coupling, nodup, positive m/n or statistical-accuracy hypothesis is allowed. Elaboration remains untested.'
 plan['new_adapter_requirements']=[
  'Independently review a new adapter for the exact published draft commit, single new module, three staged sources, 77 dependencies / 78 project imports / three prefixes, all new roots and eight imported interfaces. Existing 43af0a92, b6483ccc and 2d75404b target different scopes and must not be reused as-is.',
  'Preserve all old canonical input hashes and unchanged signature/exclusion classification. Bind all three accepted staged sources/objects separately as preservation-only immutable inputs outside the search path. They are not imports and must not be recompiled/replayed or copied into an output/project cache.',
  'Retain existing supervision, accounting, admission/runtime/output limits, first-failure stop and unique source/environment/PID/FD/limit/timing/reaping receipts. Authenticate all per-command environment/source-binding/cwd fields explicitly; replace only exact reviewed source/harness commit slots and reject placeholders/legacy authorities.',
  'Run metadata-only predicted post-output package selection before activation; repeat actual package/duplicate/shadow/sidecar/link/type checks before every child. No broad lake build, retrieval or accepted-object compilation.',
  'Complete read-only planning before fresh sole-worker/idle-reviewer coordination; retain unchanged freshness/current-facts gates and explicit nonblocking exact released-inode reuse. No creation/truncation/unlink/fallback adoption or stale timestamp refresh.',
  'Inventory every actual-owner declaration including generated/private roots, require all 16 named new theorems, reconstruct complete recursive types/bodies/inductive/recursor links and all eight imported interfaces. Exact project import set is 78; derive all new counts from exports and independently verify standard axioms and absence of unsafe/partial/project axioms.',
  'Preserve every attempt/raw diagnostic, export ordered readable chunks with reconstruction hashes, explicitly seal/stage/verify all Git blobs including .olean evidence, publish with CI skipped and stop for independent result review. No automatic retry.']
 plan['known_last_accepted_release']=dict(receipt=release_binding,accepted_evidence_commit=ACCEPTED,epoch=release['epoch'],device=33,inode=3258,directory_identity=[33,1],qualification='Historical accepted receipt only; actual common lock never opened/probed/acquired in preparation.')
 auditcontract=plan['focused_audit_expectations'];auditcontract.update(target_owner=MODULE,required_named_theorem=THEOREM,
  required_named_new_theorems=['LightEFTSpanners.JointFlagSampling.'+n for n in ROOT_THEOREMS],required_reachable_interfaces=REQUIRED,
  exact_project_module_imports=sorted(seen|{MODULE}),new_recursive_count='UNKNOWN until separately authorized future audit; no earlier count applies.')
 for key in ['prior_deterministic_closure','prior_probability_closure']:auditcontract.pop(key,None)
 plan['inherited_cache_inventory'].update(accepted_evidence_commit=ACCEPTED,canonical_journal=journal_binding,
  accepted_staged_supplements='All three accepted staged outputs are preservation-only inputs outside search roots; none is imported in this draft.')
 plan['inherited_cache_inventory'].pop('accepted_staged_object_is_separate_output_supplement',None)
 write('focused-validation-plan.json',plan)
 (HERE/'planned-commands.txt').write_text('UNEXECUTED DOCUMENTATION ONLY. No adapter/execution authority; exact reviewed draft/adapter commits must replace the two slots after separate review.\n\n'+'\n\n'.join(json.dumps(x,indent=2) for x in plan['commands'])+'\n')
 write('draft-bindings.json',dict(module=MODULE,theorem=THEOREM,**bindings,project_closure=bind(HERE/'project-dependency-bindings.json'),
  compiled_object=None,kernel_replay=None,Lean_audit=None,Lean_invocations=0,lock_acquisitions=0,status='UNELABORATED mathematical/interface draft'))
 write('preservation.json',dict(accepted_objects=accepted,source_graph=graph,inherited_protected_journal=journal_binding,latest_release_receipt=release_binding,
  source_changes_outside_new_checkpoint=False,Lean_invocations=0,common_lock_opened=False,lock_acquisitions=0,real_inventory_scans=0,retrieval=False,
  qualification='Qualified incremental source/object bindings only; no new historical IR-signature or authenticated dependency provenance claim.'))
 print(json.dumps(dict(source=bindings['source'],project_dependencies=77,expected_project_imports=78,project_prefixes=3,preserved_accepted_objects=3,
  accepted_staged_imports=0,required_imported_interfaces=len(REQUIRED),required_named_new_theorems=len(ROOT_THEOREMS),Lean_invocations=0,lock_acquisitions=0),indent=2))

if __name__=='__main__':main()
