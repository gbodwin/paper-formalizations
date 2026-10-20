"""Build a non-executable finite validation plan from already observed inputs."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
REPO=R.parents[2]
STAGE=R.parent/'staged'
TOOL=Path('/workspace/light-eft-runtime-20261020/lean-4.34.0-linux')
WORK=Path('/workspace/light-eft-paid-focused-v2-20261020/work')
OBJECTS=WORK/'objects'
MODULES=['LightEFTPaidSamplingStage.PaidFlagSerialization','LightEFTPaidSamplingStage.PaidFlagSampleComposition']
IMPORTS={'LightEFTPaidSamplingStage.PaidFlagSerialization': ['LightEFTSpanners.ControllerTrace', 'LightEFTSpanners.LinkedDistanceExecutable', 'LightEFTSpanners.LinkedDistanceInitialization', 'LightEFTSpanners.LinkedDistanceKernel', 'LightEFTSpanners.LinkedDistanceMachine', 'LightEFTSpanners.LinkedDistanceRefinement', 'LightEFTSpanners.LinkedDistanceTrace', 'LightEFTSpanners.RationalDistanceTable', 'LightEFTSpanners.RationalDistanceTest', 'LightEFTSpanners.RationalDistanceValues', 'LightSpanners.Basic', 'LightSpanners.Distance', 'LightSpanners.Greedy'], 'LightEFTPaidSamplingStage.PaidFlagSampleComposition': ['LightEFTPaidSamplingStage.PaidFlagSerialization', 'LightEFTSpanners.ControllerTrace', 'LightEFTSpanners.LinkedDistanceExecutable', 'LightEFTSpanners.LinkedDistanceInitialization', 'LightEFTSpanners.LinkedDistanceKernel', 'LightEFTSpanners.LinkedDistanceMachine', 'LightEFTSpanners.LinkedDistanceRefinement', 'LightEFTSpanners.LinkedDistanceTrace', 'LightEFTSpanners.RationalDistanceTable', 'LightEFTSpanners.RationalDistanceTest', 'LightEFTSpanners.RationalDistanceValues', 'LightEFTSpanners.StoredEdgeMembership', 'LightEFTSpanners.StoredFlagSample', 'LightEFTSpanners.StoredFlagSampleExecutable', 'LightSpanners.Basic', 'LightSpanners.Distance', 'LightSpanners.Greedy']}
FLAGS=['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true']
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def binding(p):return dict(path=str(p),bytes=p.stat().st_size,sha256=digest(p))
assert not WORK.exists()
dependencies=json.loads((R/'DEPENDENCIES-16.json').read_text())
sources=[]
for m in MODULES+['PaidFlagFixtures']:
 p=STAGE/Path(*m.split('.')).with_suffix('.lean')
 sources.append(dict(module=m,**binding(p),repository_path=str(p.relative_to(REPO))))
roots=[str(OBJECTS),'/workspace/light-eft-paid-focused-v2-inputs-20261020/objects',
       '@QUALIFIED_LOCKED_DEPENDENCY_OBJECT_ROOTS@',str(TOOL/'lib/lean')]
steps=[]
for i,m in enumerate(MODULES):
 for kind in ['compile','resolve','replay','audit']:
  target=str(OBJECTS/Path(*m.split('.')).with_suffix('.olean'))
  prior=[p+':compile' for p in MODULES[:i]]
  if kind!='compile':prior.append(m+':compile')
  row=dict(id=m+':'+kind,stage=kind,module=m,source_binding=sources[i],
   output_package_root=str(OBJECTS),expected_target=target,search_roots=roots,
   protected_completed_output_ledgers=prior,all_completed_nonobject_outputs_immutable=True,
   expected_project_imports=len(IMPORTS[m])+(kind!='compile'),expected_project_import_set=IMPORTS[m]+([] if kind=='compile' else [m]))
  if kind=='compile':row['argv']=[str(TOOL/'bin/lean'),*FLAGS,'--root='+str(STAGE),'-o',target,sources[i]['path']]
  elif kind=='replay':row['argv']=[str(TOOL/'bin/leanchecker'),'-v',m]
  else:row['required_helper']='exact singleton resolver' if kind=='resolve' else 'complete actual-owner recursive audit; all generated/private owners; no guessed owner count'
  row['output_authority']=dict(
   previous_complete_parts='protected immutable union from ledgers',
   new_target_parts=[target[:-len('.olean')]+s for s in SUFFIXES] if kind=='compile' else [],
   new_temporary='only exact current target .olean.tmp.<verified exec-authorized compiler PID>' if kind=='compile' else None,
   resolution_file=str(WORK/'resolution'/(m.rsplit('.',1)[-1]+'.json')) if kind=='resolve' else None,
   audit_directory=str(WORK/'audit'/m.rsplit('.',1)[-1]) if kind=='audit' else None)
  steps.append(row)
steps.append(dict(id='PaidFlagFixtures:elaborate',stage='compile',module='PaidFlagFixtures',source_binding=sources[2],
 output_package_root=str(OBJECTS),search_roots=roots,protected_completed_output_ledgers=[m+':compile' for m in MODULES],
 all_completed_nonobject_outputs_immutable=True,
 argv=[str(TOOL/'bin/lean'),*FLAGS,'--root='+str(STAGE),sources[2]['path']],
 output_authority='no generated object/resolution/audit output; preserve both prior output ledgers',expected_project_imports=18))
plan=dict(schema='SOURCE_REVIEW_PLAN_ONLY_v2',execution_enabled=False,
 accepted_base='a04960a8d9337df124272587cf71d31d7392bffe',reviewed_source_parent='1cd3bbf8d866c55a1b9ab1944ee58a2e535acbf7',
 source_review_correction='simp only [List.append_nil] at hs immediately after collect_trace; before hs.trans hr',
 source_bindings=sources,dependencies_binding=binding(R/'DEPENDENCIES-16.json'),existing_project_dependency_count=16,
 output_package_root=str(OBJECTS),output_namespace='LightEFTPaidSamplingStage',fresh_work_must_be_absent=True,
 package_selection='One first-package marker for both new modules; preserve first object at its original physical path/inode while compiling second',
 external_inputs_required=dependencies['direct_external_imports'],toolchain=dict(root=str(TOOL),version='4.34.0',
  release_commit='293d5d0c0c3f3dded4688b3ccd6a33939ac5102b',
  archive_sha256='caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b',
  binaries=[binding(TOOL/'bin'/n) for n in ['lean','leanchecker']]),
 resource_contract=dict(admission_GiB={'compile':3,'resolve':3,'replay':4,'audit':4},
  cpu_seconds={'compile':60,'resolve':60,'replay':60,'audit':90},wall_seconds=90,prespawn_seconds=300,
  address_space_bytes=12*1024**3,Lean_heap_MiB=5120,Lean_stack_KiB=65536,workers=1,
  stop_headroom_bytes=1024**3,RSS_stop_bytes=6*1024**3,anonymous_growth_stop_bytes=3*1024**3,
  output_bytes={'compile':16*1024**2,'audit_file':64*1024**2,'audit_total':320*1024**2},core_dump_bytes=0,
  PID_and_OOM_policy='unchanged; bind and monitor current full accounting view',
  lease='nonblocking exclusive; inherited FD verified; release only after owned reaping/ECHILD and final evidence'),
 steps=steps,readiness_blockers=[
  'Full initial cgroup hierarchy not verified: current non-initial namespace and truncated /.. mount',
  'Observed visible headroom below unchanged3/4GiB; no launch retried',
  'Local external object closure is not supplied; ordinary CI build supplies its current locked objects to the focused adapter',
  'Finite shared-package adapter and exact audit/resolver helpers are implemented in checkpoints/light-eft-paid-focused-adapter-20261020; sequential independent review is required before push/CI'],
 qualification='Frozen local source/object byte plan, not production authorization or production manifest; no historical absolute path or runtime identity resumed')
(R/'FOCUSED-PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps(dict(dependencies=16,steps=len(steps),output_package_root=str(OBJECTS),execution_enabled=False)))
