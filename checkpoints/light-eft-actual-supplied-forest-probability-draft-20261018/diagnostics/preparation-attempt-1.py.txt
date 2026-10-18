"""Read/hash exact inputs and prepare an unexecuted plan; no Lean or lock access."""
from pathlib import Path
import collections, copy, hashlib, json, os, re, subprocess, sys

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
PRIOR=ROOT/'checkpoints/light-eft-supplied-forest-probability-draft-20261018'
ADAPTER=ROOT/'checkpoints/light-eft-supplied-forest-probability-adapter-20261018'
EVIDENCE=PRIOR/'future-validation-evidence'
ACCEPTED='df18cdab7f15e5f377e6c72487e7beff6c5268e5'
FROZEN='78cb40c7837db049d645d73696f2e0b724ce8a3b'
MODULE='LightEFTActualSuppliedForestProbabilityStage.PolynomialActualFailureProbability'
THEOREM='LightEFTSpanners.StoredForestCandidates.polynomial_actual_supplied_forest_package_failure_probability'
REQUIRED=[
 'LightEFTSpanners.StoredForestCandidates.assignment_failure_le',
 'LightEFTSpanners.SampledGreedy.polynomial_supplied_forest_package_failure_probability',
 'LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests',
 'LightEFTSpanners.SampledGreedy.polynomial_inaccurate_probability',
 'LightEFTSpanners.FiniteProbability.Law.prob_mono']

def guard(event,args):
 if event=='subprocess.Popen':
  assert args[0]=='git' and args[1][0]=='git' and args[1][1]=='show','Only local Git blob reads permitted'
 if event in ['fcntl.flock','os.fork','os.posix_spawn']:raise RuntimeError('No process/compiler/lock activation in draft preparation')
 if event=='open' and isinstance(args[0],(str,bytes,os.PathLike)):
  path=os.fsdecode(args[0])
  assert path!='/tmp/distance-sparsification-single-compiler.lock' and not path.startswith(('/proc/','/sys/')),'No common-lock/resource/proc access'
sys.addaudithook(guard)

def sha(data):return hashlib.sha256(data).hexdigest()
def signature(s):return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
def bind(path,expected=None):
 p=Path(path);assert p.is_absolute() and p.is_file() and not p.is_symlink(),str(p)
 for parent in p.parents:assert not parent.is_symlink(),str(parent)
 before=p.stat();assert before.st_nlink==1
 b=p.read_bytes();after=p.stat();assert signature(before)==signature(after)
 row=dict(path=str(p),bytes=len(b),sha256=sha(b),identity=signature(after))
 if expected:
  for key in ['bytes','sha256','identity']:
   if key in expected:assert row[key]==expected[key],str(p)+' differs: '+key
 return row
def load(path):return json.loads(Path(path).read_bytes())
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
def git_bound(path,commit):
 b=subprocess.check_output(['git','show',commit+':'+str(path.relative_to(ROOT))],cwd=ROOT)
 assert path.read_bytes()==b,str(path)
 return bind(path)
def imports(path):return [line.split()[1] for line in path.read_text().splitlines() if line.startswith('import ')]

def main():
 oldplan=load(PRIOR/'focused-validation-plan.json')
 git_bound(PRIOR/'project-dependency-bindings.json','88d297fa58a15406aac6e7c0ea3c85f65965d19a')
 old=load(PRIOR/'project-dependency-bindings.json');oldrows={r['module']:r for r in old['dependencies']}
 graphpath=ROOT/'checkpoints/light-eft-clean-context-preparation-20261018/frozen-graph.json'
 graph_binding=bind(graphpath,old['frozen_source_graph']);git_bound(graphpath,ACCEPTED)
 nodes={row['module']:row for row in load(graphpath)}
 result=load(EVIDENCE/'result.json');assert result['accepted'] and result['result']['preserved']
 journal_binding=bind(EVIDENCE/'inputs.jsonl',result['result']['input_export'])
 git_bound(EVIDENCE/'inputs.jsonl',ACCEPTED)
 journal={row['path']:row for row in map(json.loads,(EVIDENCE/'inputs.jsonl').read_text().splitlines())}
 probability_source=git_bound(Path(oldplan['source']['path']),'88d297fa58a15406aac6e7c0ea3c85f65965d19a')
 probability_record=load(EVIDENCE/'compile/receipt.json')['outputs_after']['new_objects'][0]
 probability_object=bind(probability_record['path'],probability_record)
 assert probability_object['bytes']==76720 and probability_object['sha256']=='0716fe2cc66dd6657243cfe6d5d34fb83722f59818d0cdb1838be0bf2d981eeb'
 probability=dict(module=oldplan['module'],source_commit='88d297fa58a15406aac6e7c0ea3c85f65965d19a',accepted_evidence_commit=ACCEPTED,
  implementation_commit='b6483cccabdf4afdbb8004a768afe8ea9ed0ff32',source=probability_source,object=probability_object,
  direct_project_imports=imports(Path(probability_source['path'])),qualified_acceptance='User reports independent qualified incremental acceptance; source/log/hash reconciliation only here, no execution.')
 manual={oldplan['module']:probability}
 deterministic=oldrows['LightEFTSuppliedForestStage.SuppliedForestGoodEvent']
 manual[deterministic['module']]=deterministic
 source=HERE/'staged'/Path(*MODULE.split('.')).with_suffix('.lean')
 assert not re.search(rb'\b(sorry|admit|axiom|unsafe|partial)\b',source.read_bytes())
 todo=imports(source);seen=set()
 while todo:
  name=todo.pop()
  if name in seen:continue
  seen.add(name)
  node=manual.get(name,nodes.get(name));assert node is not None,name
  todo.extend(node.get('direct_project_imports',node.get('project_imports',[])))
 assert len(seen)==344 and set(oldrows)<=seen and len(seen-set(oldrows)-set(manual))==130
 objroot=Path(oldrows['LightEFTSpanners.Basic']['object']['path']).parents[1]
 rows=[]
 for name in sorted(seen):
  if name in oldrows:
   row=copy.deepcopy(oldrows[name]);bind(row['source']['path'],row['source']);bind(row['object']['path'],row['object'])
   row['part_of_accepted_probability_dependency_closure']=True
  elif name in manual:row=copy.deepcopy(manual[name])
  else:
   node=nodes[name];src=bind(ROOT/node['path'],node);obj=objroot/Path(*name.split('.')).with_suffix('.olean')
   assert str(obj) in journal,'Missing protected existing object: '+str(obj)
   ob=bind(obj,journal[str(obj)])
   row=dict(module=name,source_commit=FROZEN,source=src,object=ob,direct_project_imports=node['project_imports'],prior_protected_object=journal[str(obj)],
    part_of_accepted_probability_dependency_closure=False)
  rows.append(row)
 assert sum(x['source_commit']==FROZEN for x in rows)==342
 closure=dict(status='Source import closure and exact existing object-byte reconciliation only; no Lean/environment query or authenticated provenance',
  direct_imports=imports(source),dependencies=rows,total_project_dependencies=344,existing_frozen_modules=342,accepted_staged_dependency_modules=2,
  preserved_previous_dependency_count=213,additional_frozen_modules=sorted(seen-set(oldrows)-set(manual)),
  namespace_counts=dict(collections.Counter(x['module'].split('.')[0] for x in rows)),frozen_source_graph=graph_binding,
  inherited_protected_journal=journal_binding,accepted_probability_evidence_commit=ACCEPTED)
 write('project-dependency-bindings.json',closure)
 jsonl=HERE/'project-dependency-bindings.jsonl'
 jsonl.write_text(''.join(json.dumps(x,separators=(',',':'))+'\n' for x in rows))
 export=HERE/'project-closure-export';export.mkdir(exist_ok=False);parts=[];buffer=bytearray()
 def flush():
  if not buffer:return
  p=export/('part-%04d.txt'%len(parts));data=bytes(buffer);p.write_bytes(data)
  parts.append(dict(path=p.name,bytes=len(data),sha256=sha(data)));buffer.clear()
 for line in jsonl.read_bytes().splitlines(keepends=True):
  if buffer and len(buffer)+len(line)>200000:flush()
  buffer.extend(line)
 flush();assert b''.join((export/x['path']).read_bytes() for x in parts)==jsonl.read_bytes()
 (export/'manifest.json').write_text(json.dumps(dict(source=str(jsonl),bytes=jsonl.stat().st_size,sha256=sha(jsonl.read_bytes()),row_aligned=True,target_bytes=200000,parts=parts),indent=2)+'\n')

 audit=(PRIOR/'staged/PolynomialSuppliedForestProbabilityAudit.lean').read_text().replace(oldplan['module'],MODULE).replace(oldplan['theorem'],THEOREM)
 needle='  let required : Array Name := #['
 audit='\n'.join(('  let required : Array Name := #['+', '.join('"'+n+'".toName' for n in REQUIRED)+']') if line.startswith(needle) else line for line in audit.splitlines())+'\n'
 audit=audit.replace('Missing supplied-forest theorem','Missing actual supplied-forest probability theorem')
 auditpath=HERE/'staged/PolynomialActualSuppliedForestProbabilityAudit.lean';auditpath.write_text(audit)
 resolverpath=HERE/'staged/ResolvePolynomialActualSuppliedForestTarget.lean'
 resolverpath.write_text((PRIOR/'staged/ResolvePolynomialSuppliedForestTarget.lean').read_text().replace(oldplan['module'],MODULE))
 bindings=dict(source=bind(source),audit=bind(auditpath),resolver=bind(resolverpath))
 work=ROOT/'.lake/actual-supplied-forest-probability-954a493204fe4fbc9da5163e52349120';evidence=HERE/'future-validation-evidence'
 assert not work.exists() and not evidence.exists()
 objects=work/'objects';target=objects/Path(*MODULE.split('.')).with_suffix('.olean')
 from_root=oldplan['commands'][0]['environment']['LEAN_PATH'].split(':')
 roots=[objects]+list(map(Path,from_root));assert len(roots)==len(set(map(str,roots)))
 sys.path.insert(0,str(ADAPTER))
 from package_selection import selected_path
 predictions=[]
 for row in rows:
  selected=selected_path(roots,row['module'],predicted_dirs=[objects/MODULE.split('.')[0]],predicted_files=[target])
  assert str(selected)==row['object']['path'],row['module']
  predictions.append(dict(module=row['module'],selected=str(selected),expected=row['object']['path']))
 assert selected_path(roots,MODULE,predicted_dirs=[objects/MODULE.split('.')[0]],predicted_files=[target])==target
 write('package-layout-prediction.json',dict(status='Metadata-only prediction; no future output root created',roots=list(map(str,roots)),
  dependencies=predictions,new_module=MODULE,predicted_new_object=str(target),dependency_selection_matches=len(rows),future_work_root_exists=False))
 releasepath=EVIDENCE/'lease.json';git_bound(releasepath,ACCEPTED)
 release_binding=bind(releasepath,dict(bytes=718,sha256='f1cb1eb90fcaa82f55c84d2be396f561794e6b83096a9e3970e3424d0f9cf6ef'))
 release=load(releasepath);assert release['state']=='released' and release['kernel_echild'] and release['epoch']=='f8ff4af575274e8c9aec76c264ef7726'
 assert (release['device'],release['inode'])==(33,3258)
 accepted_rows=[x for x in rows if x['module'] in manual]
 write('accepted-theorem-bindings.json',dict(accepted_modules=accepted_rows,probability_recursive_audit=dict(constants=51084,opaque_bodies=44,
  raw_export=bind(ROOT/'checkpoints/light-eft-supplied-forest-probability-result-20261018/artifacts/audit/ci-evidence/recursive-dependencies.tsv',dict(bytes=33664860,sha256='d7a48b230dfb85a625faa20f50f8606f37e00e77df94a81a9971414fb045a4ab'))),
  review='User-reported independent qualified incremental acceptance; preservation/hash reconciliation only, no fresh replay/audit.'))
 plan=copy.deepcopy(oldplan)
 plan.update(status='DRAFT_PLAN_ONLY; no execution authority or adapted executable wrapper',module=MODULE,theorem=THEOREM,
  **bindings,new_object=str(target),new_object_hash=None,future_work_root=str(work),future_evidence_root=str(evidence),work_and_evidence_created=False,
  accepted_probability_dependency=probability,accepted_deterministic_dependency=deterministic,
  project_closure=bind(HERE/'project-dependency-bindings.json'),project_dependency_count=344,
  expected_project_module_import_count_including_new_target=345,
  project_namespace_prefixes=oldplan['project_namespace_prefixes']+[MODULE.split('.')[0]])
 env=copy.deepcopy(oldplan['commands'][0]['environment']);env['LEAN_PATH']=':'.join(map(str,roots))
 env['LEAN_SRC_PATH']=str(HERE/'staged')+':'+env['LEAN_SRC_PATH']
 flags=oldplan['commands'][0]['argv'][1:6];lean=oldplan['commands'][0]['argv'][0];checker=oldplan['commands'][2]['argv'][0]
 argvs=[[lean]+flags+['--root='+str(HERE/'staged'),'-o',str(target),str(source)],
  [lean]+flags+[str(resolverpath)],[checker,'-v',MODULE],[lean]+flags+[str(auditpath)]]
 roles=[['source'],['resolver','source'],['source'],['audit','source']]
 plan['commands']=[]
 for i,stage in enumerate(['compile','resolve','replay','audit']):
  stageenv=copy.deepcopy(env)
  if stage=='resolve':stageenv.update(LIGHTEFT_CHECKER_TARGET=MODULE,LIGHTEFT_CHECKER_RESOLUTION_FILE=str(work/'resolution.json'))
  if stage=='replay':
   stageenv.pop('MIMALLOC_VERBOSE');stageenv.update(LEAN_NUM_THREADS='1',LEAN_STACK_SIZE_KB='65536')
  config=dict(argv=argvs[i],env=stageenv,stage=stage)
  length=len(json.dumps(config).encode());assert length<=4096,(stage,length)
  plan['commands'].append(dict(stage=stage,argv=argvs[i],environment=stageenv,submitted_sources=[bindings[k] for k in roles[i]],
   cwd=str(work/'audit' if stage=='audit' else work),visible_admission_bytes=oldplan['commands'][i]['visible_admission_bytes'],executed=False,
   launcher_config_bytes_with_placeholders=length))
 plan['interface_review']='Source-only contract analysis: assignment_failure_le for the entire four-part predicate, followed by accepted probability theorem; confirm rational casts, output unfolding and local lets during any separately authorized future elaboration.'
 plan['new_adapter_requirements']=[
  'Separately review an executable adapter bound to the exact new draft commit, '+MODULE+', '+THEOREM+', three sources, 344 dependencies, 345 project imports, five prefixes and new work/evidence paths. Neither b6483ccc nor 2d75404b supports this scope as-is.',
  'Retain existing reviewed process supervision, accounting, admission floors, memory/CPU/wall/output limits, first-failure stop, unique source/environment/PID/FD/start/finish/reaping receipts and complete raw diagnostics. No accepted-object recompilation or automatic retry.',
  'Authenticate both accepted output objects as immutable exact path/bytes/hash/identity supplements. Keep all old cache/input hashes authoritative; no whole-root admission, root replacement, copying into a project cache, rebuild or retrieval. The 130 additional frozen objects already appear in the protected inventory.',
  'Translate per-command environment/submitted_sources/cwd explicitly into env/sources/full source_bindings/cwd. Fill only the exact reviewed draft/adapter commit placeholders after approval; reject remaining placeholders and old origin commits as new source authority.',
  'Validate predicted post-output physical packages before activation and actual selection before every child; retain independent duplicate/shadow/target-prefix/sidecar/link/type and exact-command checks.',
  'Finish read-only planning before fresh sole-worker/idle-reviewer coordination. Preserve the unchanged less-than-60-second current-facts checks. Reuse only the exact separately authorized latest released inode/receipt; no create, truncate, unlink, stale timestamp refresh or unknown-inode adoption.',
  'Independently reconstruct every actual-owner root and complete recursive types/bodies/inductive/recursor closure; enforce exact 345 project imports across all five prefixes and all five required interfaces; never trust printed PASS/counts alone.',
  'Export ordered readable chunks with reconstruction hashes and explicitly seal/stage/verify every Git blob, including ignored .olean evidence; publish only with CI skipped and pause for independent result review.']
 plan['known_last_accepted_release']=dict(receipt=release_binding,accepted_evidence_commit=ACCEPTED,device=33,inode=3258,directory_identity=[33,1],epoch=release['epoch'],
  qualification='Historical accepted receipt only; no actual common-lock open, probe or acquisition in this preparation.')
 auditcontract=plan['focused_audit_expectations'];auditcontract.update(target_owner=MODULE,required_named_theorem=THEOREM,
  required_reachable_interfaces=REQUIRED,exact_project_module_imports=sorted(seen|{MODULE}),
  prior_deterministic_closure='Preserved accepted dependency evidence only; not a fresh audit or the new closure.',
  prior_probability_closure='51084 constants / d7a48b230dfb85a625faa20f50f8606f37e00e77df94a81a9971414fb045a4ab; preserved evidence, not the new closure.',
  new_recursive_count='UNKNOWN until separately authorized future audit; do not substitute 51084 or 22362.')
 plan['inherited_cache_inventory'].update(accepted_evidence_commit=ACCEPTED,canonical_journal=journal_binding,accepted_staged_object_is_separate_output_supplement=True,
  accepted_staged_supplements='Both deterministic b5e18c... and probability 0716fe... are exact immutable output bindings; only first was in prior runtime input journal.')
 write('focused-validation-plan.json',plan)
 (HERE/'planned-commands.txt').write_text('UNEXECUTED PLAN ONLY. Not an activation script. Bind exact reviewed draft and separately reviewed adapter commits first.\n\n'+'\n\n'.join(json.dumps(x,indent=2) for x in plan['commands'])+'\n')
 interface_modules=['LightEFTSpanners.StoredForestOutputLaw','LightEFTSpanners.StoredOutputLaw','LightEFTSpanners.StoredForestAssignment',
  'LightEFTSpanners.StoredForestCandidatesExecutable','LightEFTSpanners.StoredForestComponentIndices','LightEFTSpanners.VotingOutput']+sorted(manual)
 byname={x['module']:x for x in rows};write('interface-bindings.json',[byname[x] for x in interface_modules])
 (HERE/'interface-declarations.txt').write_text('\n\n'.join('MODULE '+x+'\nSOURCE '+byname[x]['source']['path']+'\n'+Path(byname[x]['source']['path']).read_text() for x in interface_modules))
 write('draft-bindings.json',dict(module=MODULE,theorem=THEOREM,**bindings,project_closure=bind(HERE/'project-dependency-bindings.json'),
  compiled_object=None,kernel_replay=None,Lean_audit=None,Lean_invocations=0,lock_acquisitions=0,status='DRAFT_UNELABORATED; mathematical/interface/plan review required'))
 write('preservation.json',dict(accepted_objects=[dict(module=x['module'],object=bind(x['object']['path'],x['object'])) for x in accepted_rows],
  preserved_prior_dependency_bindings=213,additional_preexisting_frozen_bindings=130,source_graph=graph_binding,latest_released_receipt=release_binding,
  common_lock_opened=False,common_lock_acquired=False,Lean_invocations=0,inventory_scan=False,retrieval=False,source_promotion=False,
  provenance='Qualified incremental local bindings; no new historical-signature or authenticated-dependency provenance claim.'))
 print(json.dumps(dict(draft=bindings['source'],dependencies=344,existing_frozen_modules=342,accepted_staged_modules=2,
  project_imports_including_target=345,additional_frozen_dependencies=130,namespace_counts=closure['namespace_counts'],
  package_prediction='all dependency and new target selections match',Lean_invocations=0,lock_acquisitions=0,new_work_root_created=False),indent=2))

if __name__=='__main__':main()
