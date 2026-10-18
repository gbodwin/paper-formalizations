"""Draft evidence preparation only: read/hash sources and existing objects.

No Lean, compiler/checker, lock acquisition, inventory scan or activation API.
Writes draft bindings and unexecuted audit/resolver sources in this checkpoint.
"""
from pathlib import Path
import collections,hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
ACCEPTED=ROOT/'checkpoints/light-eft-supplied-forest-package-20261018'
sys.path.insert(0,str(ACCEPTED))
from contracts import bind
from package_selection import selected_path

NEW_MODULE='LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability'
NEW_THEOREM='LightEFTSpanners.SampledGreedy.polynomial_supplied_forest_package_failure_probability'
REQUIRED=[
 'LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests',
 'LightEFTSpanners.SampledGreedy.polynomial_inaccurate_probability',
 'LightEFTSpanners.FiniteProbability.Law.prob_mono']

def write(name,value):
 (HERE/name).write_text(json.dumps(value,indent=2)+'\n')

def main():
 prior_inputs={r['path']:r for r in map(json.loads,(ACCEPTED/'production-evidence/inputs.jsonl').read_text().splitlines())}
 envpath=ROOT/'checkpoints/light-eft-supplied-forest-draft-20261018/environment.json'
 blob=subprocess.check_output(['git','show','40029953e9e53525f0f1f431d6d56333b05183a3:'+str(envpath.relative_to(ROOT))],cwd=ROOT)
 assert envpath.read_bytes()==blob
 graphpath=ROOT/'checkpoints/light-eft-clean-context-preparation-20261018/frozen-graph.json'
 graph_binding=bind(graphpath,{'sha256':json.loads(blob)['frozen_graph_sha256']})
 nodes={r['module']:r for r in json.loads(graphpath.read_text())}
 old=json.loads((ROOT/'checkpoints/light-eft-supplied-forest-draft-20261018/accepted-imports.json').read_text())
 oldset={r['module'] for r in old['bindings']}
 def closure(seeds):
  seen=set();todo=list(seeds)
  while todo:
   name=todo.pop()
   if name in seen:continue
   seen.add(name);assert name in nodes,name;todo.extend(nodes[name]['project_imports'])
  return seen
 accepted_source=ACCEPTED/'staged/LightEFTSuppliedForestStage/SuppliedForestGoodEvent.lean'
 seeds=[s.split()[1] for s in accepted_source.read_text().splitlines() if s.startswith('import ')]
 assert closure(seeds)==oldset and len(oldset)==196
 names=sorted(oldset|closure(['LightEFTSpanners.ComputableVotingSamples']));assert len(names)==212
 spec=json.loads((ACCEPTED/'execution-proposal.json').read_text());objroot=Path(spec['accepted_project_objects']);rows=[]
 for name in names:
  source=nodes[name];source_binding=bind(ROOT/source['path'],source)
  obj=objroot/Path(*name.split('.')).with_suffix('.olean');assert str(obj) in prior_inputs,name
  object_binding=bind(obj,prior_inputs[str(obj)])
  rows.append(dict(module=name,source_commit='78cb40c7837db049d645d73696f2e0b724ce8a3b',source=source_binding,object=object_binding,
   direct_project_imports=source['project_imports'],part_of_prior_196=name in oldset,prior_protected_object=prior_inputs[str(obj)]))
 accepted_record=json.loads((ROOT/'checkpoints/light-eft-supplied-forest-package-attempt-20261018/produced-object-bindings.json').read_text())[0]['original']
 assert accepted_record['sha256']=='b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18'
 actual=bind(accepted_record['path'],accepted_record)
 accepted_bind=bind(accepted_source,{'bytes':4988,'sha256':'6356a3b369813a155e824e471b0f7a48d29a66fb117db41eca767ed3300febee'})
 rows.append(dict(module='LightEFTSuppliedForestStage.SuppliedForestGoodEvent',source_commit='2d75404bfd140d0e8ecb13d3c2554b853b9a1640',accepted_evidence_commit='7eedd5b3c7860cf473f5deff3b4ed369f19e6e61',source=accepted_bind,object=actual,original_accepted_binding=accepted_record,direct_project_imports=seeds,part_of_prior_196=False,qualified_acceptance='Independent qualified incremental review reported by user; no new compile/replay here.'))
 rows.sort(key=lambda r:r['module'])
 closure_path=HERE/'project-dependency-bindings.json'
 write(closure_path.name,dict(status='Source/import-graph and existing object-byte reconciliation only; not a Lean check or authenticated provenance',dependencies=rows,direct_imports=['LightEFTSuppliedForestStage.SuppliedForestGoodEvent','LightEFTSpanners.ComputableVotingSamples'],existing_frozen_modules=212,accepted_staged_dependency_modules=1,total_project_dependencies=213,additional_frozen_modules=sorted(set(names)-oldset),namespace_counts=dict(collections.Counter(r['module'].split('.')[0] for r in rows)),frozen_source_graph=graph_binding,frozen_graph_expected_hash_origin=bind(envpath)))
 source=HERE/'staged/LightEFTSuppliedForestProbabilityStage/PolynomialFailureProbability.lean';draft=bind(source)
 assert not re.search(rb'\b(sorry|admit|axiom|unsafe|partial)\b',source.read_bytes())
 audit=(ACCEPTED/'staged/SuppliedForestGoodEventAudit.lean').read_text().replace('LightEFTSuppliedForestStage.SuppliedForestGoodEvent',NEW_MODULE).replace('LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests',NEW_THEOREM)
 needle='  IO.FS.writeFile "ci-evidence/actual-owner-inventory.tsv" inventory'
 check='  -- Require the exact reviewed deterministic and probability interfaces.\n  let required : Array Name := #['+', '.join('"'+n+'".toName' for n in REQUIRED)+']\n  for n in required do\n    unless visited.contains n do issues := issues.push s!"Missing required reachable interface: {n}"\n'
 assert needle in audit;audit=audit.replace(needle,check+needle)
 (HERE/'staged/PolynomialSuppliedForestProbabilityAudit.lean').write_text(audit)
 resolver=(ACCEPTED/'staged/ResolveSuppliedForestTarget.lean').read_text().replace('LightEFTSuppliedForestStage.SuppliedForestGoodEvent',NEW_MODULE)
 (HERE/'staged/ResolvePolynomialSuppliedForestTarget.lean').write_text(resolver)
 work=ROOT/'.lake/supplied-forest-probability-4c8d7848fa3c4b09bd648c9c587a0f83';objects=work/'objects';target=objects/Path(*NEW_MODULE.split('.')).with_suffix('.olean')
 roots=[objects]+list(map(Path,spec['environment']['LEAN_PATH'].split(':')))
 assert len(roots)==len(set(map(str,roots))) and not work.exists()
 predicted=[]
 for row in rows:
  choice=selected_path(roots,row['module'],predicted_dirs=[objects/NEW_MODULE.split('.')[0]],predicted_files=[target])
  assert str(choice)==row['object']['path'],row['module']
  predicted.append(dict(module=row['module'],selected=str(choice),expected=row['object']['path']))
 assert selected_path(roots,NEW_MODULE,predicted_dirs=[objects/NEW_MODULE.split('.')[0]],predicted_files=[target])==target
 write('package-layout-prediction.json',dict(status='Metadata-only prediction, no output directory created or compiler invoked',roots=list(map(str,roots)),dependencies=predicted,new_module=NEW_MODULE,predicted_new_object=str(target),new_top_level=NEW_MODULE.split('.')[0],accepted_top_level='LightEFTSuppliedForestStage',legacy_top_levels=['LightEFTSpanners','LightSpanners'],dependency_selection_matches=213,future_work_root_exists=False))
 prior_closure=ROOT/'checkpoints/light-eft-supplied-forest-package-attempt-20261018/audit-raw/recursive-dependencies.tsv'
 write('accepted-theorem-binding.json',dict(accepted_evidence_commit='7eedd5b3c7860cf473f5deff3b4ed369f19e6e61',implementation_commit='2d75404bfd140d0e8ecb13d3c2554b853b9a1640',source=accepted_bind,object=actual,original_accepted_binding=accepted_record,existing_recursive_closure=bind(prior_closure,{'bytes':10483642,'sha256':'a3bf42e240b49ddfd17a6566f5b51b546c465de25a4441a3a701c168298e4260'}),existing_closure_constants=22362,qualification='Read-only preservation/binding only; accepted object neither recompiled nor promoted.'))
 write('draft-bindings.json',dict(module=NEW_MODULE,theorem=NEW_THEOREM,source=draft,audit=bind(HERE/'staged/PolynomialSuppliedForestProbabilityAudit.lean'),resolver=bind(HERE/'staged/ResolvePolynomialSuppliedForestTarget.lean'),project_closure=bind(closure_path),compiled_object=None,kernel_replay=None,Lean_audit=None,Lean_invocations=0,lock_acquisitions=0,status='DRAFT_UNELABORATED; independent mathematical/interface/plan review required'))
 print(json.dumps(dict(draft_sha256=draft['sha256'],draft_bytes=draft['bytes'],project_dependencies=len(rows),new_frozen_dependencies=len(set(names)-oldset),accepted_object_sha256=actual['sha256'],prediction='all 213 dependencies plus draft target select intended package roots',Lean_invocations=0,lock_acquisitions=0),indent=2))

if __name__=='__main__':main()
