"""Read-only plan binding/negative-contract checks. Never starts any child."""
from pathlib import Path
import copy,hashlib,json
R=Path(__file__).resolve().parent
MODULES=['LightEFTPaidSamplingStage.PaidFlagSerialization','LightEFTPaidSamplingStage.PaidFlagSampleComposition']
IMPORTS={'LightEFTPaidSamplingStage.PaidFlagSerialization': ['LightEFTSpanners.ControllerTrace', 'LightEFTSpanners.LinkedDistanceExecutable', 'LightEFTSpanners.LinkedDistanceInitialization', 'LightEFTSpanners.LinkedDistanceKernel', 'LightEFTSpanners.LinkedDistanceMachine', 'LightEFTSpanners.LinkedDistanceRefinement', 'LightEFTSpanners.LinkedDistanceTrace', 'LightEFTSpanners.RationalDistanceTable', 'LightEFTSpanners.RationalDistanceTest', 'LightEFTSpanners.RationalDistanceValues', 'LightSpanners.Basic', 'LightSpanners.Distance', 'LightSpanners.Greedy'], 'LightEFTPaidSamplingStage.PaidFlagSampleComposition': ['LightEFTPaidSamplingStage.PaidFlagSerialization', 'LightEFTSpanners.ControllerTrace', 'LightEFTSpanners.LinkedDistanceExecutable', 'LightEFTSpanners.LinkedDistanceInitialization', 'LightEFTSpanners.LinkedDistanceKernel', 'LightEFTSpanners.LinkedDistanceMachine', 'LightEFTSpanners.LinkedDistanceRefinement', 'LightEFTSpanners.LinkedDistanceTrace', 'LightEFTSpanners.RationalDistanceTable', 'LightEFTSpanners.RationalDistanceTest', 'LightEFTSpanners.RationalDistanceValues', 'LightEFTSpanners.StoredEdgeMembership', 'LightEFTSpanners.StoredFlagSample', 'LightEFTSpanners.StoredFlagSampleExecutable', 'LightSpanners.Basic', 'LightSpanners.Distance', 'LightSpanners.Greedy']}
FLAGS=['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true']
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig']
def require(ok,message):
 if not ok:raise ValueError(message)
def check(p):
 require(p['execution_enabled'] is False,'Plan is not execution authority')
 require(p['existing_project_dependency_count']==16,'Dependency scope differs')
 root=Path(p['output_package_root'])
 require(p['output_namespace']=='LightEFTPaidSamplingStage','First-package namespace differs')
 require(len(p['steps'])==9,'Finite schedule differs')
 for i,m in enumerate(MODULES):
  target=str(root/Path(*m.split('.')).with_suffix('.olean'))
  for j,kind in enumerate(['compile','resolve','replay','audit']):
   row=p['steps'][i*4+j]
   require(row['id']==m+':'+kind,'Ledger-producing stage identity differs')
   require((row['module'],row['stage'])==(m,kind),'Reordered module/stage')
   expected=IMPORTS[m]+([] if kind=='compile' else [m])
   require(row['expected_project_imports']==len(expected) and row['expected_project_import_set']==expected,'Per-module import set differs')
   require(row['output_package_root']==str(root) and row['expected_target']==target,'Split output package')
   require(row['search_roots'][0]==str(root),'Shared first-package root is not first')
   prior=[x+':compile' for x in MODULES[:i]]+([] if kind=='compile' else [m+':compile'])
   require(row['protected_completed_output_ledgers']==prior,'Lost completed object ledger')
   require(set(prior)<={s['id'] for s in p['steps'][:i*4+j]},'Ledger does not refer to an earlier producing stage')
   require(row['all_completed_nonobject_outputs_immutable'] is True,'Completed resolution/audit/evidence can change')
   if kind=='compile':
    require(row['argv'][1:6]==FLAGS and row['argv'][-3:]==['-o',target,row['source_binding']['path']],'Compile command differs')
    require(row['output_authority']['new_target_parts']==[target[:-len('.olean')]+s for s in SUFFIXES],'Unbounded/new output authority')
   else:require(not row['output_authority']['new_target_parts'],'Noncompile object output allowed')
 f=p['steps'][8]
 require(f['module']=='PaidFlagFixtures' and '-o' not in f['argv'],'Fixtures generate an extra object package')
 require(f['output_package_root']==str(root) and f['search_roots'][0]==str(root),'Fixtures lose shared package')
 require(f['protected_completed_output_ledgers']==[m+':compile' for m in MODULES],'Fixture loses prior output')
 require(f['all_completed_nonobject_outputs_immutable'] is True,'Fixture can change completed evidence')
 rc=p['resource_contract']
 require(rc['admission_GiB']==dict(compile=3,resolve=3,replay=4,audit=4),'Admission changed')
 require(rc['cpu_seconds']==dict(compile=60,resolve=60,replay=60,audit=90),'CPU changed')
 require((rc['wall_seconds'],rc['prespawn_seconds'],rc['workers'])==(90,300,1),'Wall/preflight/worker changed')
 require((rc['stop_headroom_bytes'],rc['RSS_stop_bytes'],rc['anonymous_growth_stop_bytes'])==(1024**3,6*1024**3,3*1024**3),'Memory stops changed')
def verify_binding(row):
 raw=Path(row['path']).read_bytes()
 require(len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256'],'Byte binding differs: '+row['path'])
def main():
 p=json.loads((R/'FOCUSED-PLAN.json').read_text());check(p)
 require(not Path(p['output_package_root']).parent.exists(),'Fresh work root already exists')
 verify_binding(p['dependencies_binding'])
 d=json.loads(Path(p['dependencies_binding']['path']).read_text());require(d['count']==len(d['dependencies'])==16,'16 dependencies missing')
 repo=R.parents[2]
 for row in d['dependencies']:
  verify_binding(dict(row['source'],path=str(repo/row['source']['path'])))
  verify_binding(row['object'])
 for row in p['source_bindings']+p['toolchain']['binaries']:verify_binding(row)
 source=Path(p['source_bindings'][0]['path']).read_text()
 require('have hs := collect_trace keys bits hlen []\n  simp only [List.append_nil] at hs\n' in source,'Reviewed intermediate-state fix absent')
 mutations=[
  lambda q:q.update(execution_enabled=True),
  lambda q:q.update(existing_project_dependency_count=15),
  lambda q:q['steps'][4].update(output_package_root='/other/objects'),
  lambda q:q['steps'][4].update(protected_completed_output_ledgers=[]),
  lambda q:q['steps'][4]['search_roots'].reverse(),
  lambda q:q['steps'][4]['output_authority']['new_target_parts'].append('/foreign/Other.olean'),
  lambda q:q['resource_contract']['admission_GiB'].update(compile=2),
  lambda q:q['resource_contract']['cpu_seconds'].update(compile=90),
  lambda q:q['resource_contract'].update(workers=2),
  lambda q:q['steps'][8].update(protected_completed_output_ledgers=[])]
 mutations.append(lambda q:q['steps'][0].update(id='unrelated-stage'))
 mutations.append(lambda q:q['steps'][0].update(expected_project_imports=16,expected_project_import_set=sorted(IMPORTS[MODULES[1]][:-1])))
 mutations.append(lambda q:q['steps'][5].update(expected_project_import_set=IMPORTS[MODULES[0]]+[MODULES[1]]))
 for mutate in mutations:
  q=copy.deepcopy(p);mutate(q)
  try:check(q)
  except ValueError:pass
  else:raise AssertionError('Bad plan accepted')
 result=dict(bound_existing_dependencies=16,source_bindings=3,positive_plan_pass=True,rejected_negative_plans=len(mutations),reviewed_append_nil_fix_present=True,one_shared_output_root=True,first_object_preservation_required=True,Lean_children=0,qualification='Read-only source/file and plan-contract checks only; eight Lean fixtures remain uncompiled')
 (R/'PLAN-CHECK-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result))
if __name__=='__main__':main()
