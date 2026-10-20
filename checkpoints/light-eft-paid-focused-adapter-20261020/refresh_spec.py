"""Offline reviewed-source binding refresh; never launches a compiler or CI."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent;ROOT=R.parents[1]
BASE=ROOT/'checkpoints/light-eft-canonical-output-adapter-20261020'
def row(p,**extra):
 raw=p.read_bytes();return dict(path=str(p.relative_to(ROOT)),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),**extra)
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
workflow=ROOT/'.github/workflows/lean.yml'
# The two existing gates bind workflow bytes. Refresh only that byte row and,
# in the canonical spec, its binding to the decoder spec whose row changed.
decoder=ROOT/'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019/ci-spec.json'
for p in [decoder,BASE/'ci-spec.json']:
 s=json.loads(p.read_text())
 for i,r in enumerate(s['engine_files']):
  if r['path'] in [str(workflow.relative_to(ROOT)),str(decoder.relative_to(ROOT))]:s['engine_files'][i]=row(ROOT/r['path'])
 save(p,s)
accepted=json.loads((BASE/'ci-spec.json').read_text())
deps=json.loads((ROOT/'checkpoints/light-eft-paid-sampling-20261020/focused-v2/DEPENDENCIES-16.json').read_text())
staged=ROOT/'checkpoints/light-eft-paid-sampling-20261020/staged'
roles={'serialization':staged/'LightEFTPaidSamplingStage/PaidFlagSerialization.lean',
 'composition':staged/'LightEFTPaidSamplingStage/PaidFlagSampleComposition.lean','fixtures':staged/'PaidFlagFixtures.lean',
 'resolver':R/'staged/ResolveFocusedTarget.lean','serialization_audit':R/'staged/SerializationAudit.lean',
 'composition_audit':R/'staged/CompositionAudit.lean'}
engines=[*BASE.glob('*.py'),*R.glob('*.py'),ROOT/'scripts/LightEFTCgroup.py',ROOT/'scripts/LightEFTProcessLifecycle.py',workflow,ROOT/'lake-manifest.json',ROOT/'lean-toolchain']
spec=dict(scope='PAID_FLAG_SERIALIZATION_AND_STORED_FILTER_COMPOSITION',source_base='a04960a8d9337df124272587cf71d31d7392bffe',
 toolchain='leanprover/lean4:v4.34.0',tool_hashes=accepted['tool_hashes'],pins=accepted['pins'],
 staged_root=str(staged.relative_to(ROOT)),sources=[row(p,role=role) for role,p in roles.items()],
 dependencies=[dict(module=x['module'],**x['source']) for x in deps['dependencies']],
 engine_files=[row(p) for p in sorted(set(engines))],
 execution_order=['serialization:compile','serialization:resolve','serialization:replay','serialization:audit',
 'composition:compile','composition:resolve','composition:replay','composition:audit','fixtures:compile'],
 existing_dependencies=16,serialization_project_imports=14,composition_project_imports=18,
 resource_policy='Accepted a04960a8 engine and limits unchanged; complete receipt verification retained',
 dependency_qualification='Fresh ordinary-CI build; retained review carriers are not production inputs')
save(R/'ci-spec.json',spec)
print(json.dumps(dict(sources=len(spec['sources']),dependencies=len(spec['dependencies']),engine_files=len(spec['engine_files']))))
