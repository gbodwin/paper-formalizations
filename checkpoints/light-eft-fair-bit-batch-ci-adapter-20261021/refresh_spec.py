"""Offline exact binding refresh. No compiler, admission, remote write or CI."""
from pathlib import Path
import ast,hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
CONTRACT=ast.literal_eval((HERE/'finite_contract.py').read_text().split('CONTRACT=',1)[1])
NAMES=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
       'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020']
def row(path,**extra):
    raw=path.read_bytes()
    return dict(path=str(path.relative_to(ROOT)),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),**extra)
def save(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
prior=[]
for name in NAMES:
    path=ROOT/'checkpoints'/name/'ci-spec.json'
    data=json.loads(path.read_text())
    for i,r in enumerate(data['engine_files']):
        if r['path']=='.github/workflows/lean.yml' or any(r['path']=='checkpoints/'+n+'/ci-spec.json' for n in NAMES):
            data['engine_files'][i]=row(ROOT/r['path'])
    save(path,data);prior.append(data)
bridge=prior[-1]
deps=list(bridge['dependencies'])
p=next(r for r in bridge['sources'] if r['role']=='bridge')
deps.append(dict(module='LightEFTPaidJointBridgeStage.SuppliedResponseJointBridge',path=p['path'],bytes=p['bytes'],sha256=p['sha256'],origin='bridge'))
sources=[]
for m,role,audit in zip(CONTRACT['modules'],['flat','sampler','independent'],['FlatTapeAudit','FairBitAudit','IndependentTapeAudit'],strict=True):
    sources.append(row(ROOT/CONTRACT['reviewed_sources'][m]['path'],role=role))
    sources.append(row(HERE/'staged'/(audit+'.lean'),role=role+'_audit'))
sources.append(row(HERE/'staged/ResolveBatchTarget.lean',role='resolver'))
paths={p for p in HERE.glob('*.py')}
paths.update(p for p in HERE.glob('*.json') if p.name!='ci-spec.json')
paths.update(HERE.glob('*.md'))
for name,data in zip(NAMES,prior,strict=True):
    paths.add(ROOT/'checkpoints'/name/'ci-spec.json')
    paths.update(ROOT/r['path'] for r in data['engine_files'])
    values=data['sources'] if isinstance(data['sources'],list) else data['sources'].values()
    paths.update(ROOT/r['path'] for r in values)
paths.update([ROOT/'.github/workflows/lean.yml',ROOT/'lake-manifest.json',ROOT/'lean-toolchain'])
spec=dict(scope='REVIEWED_FLAT_TAPE_FAIR_BIT_BATCH_EXACT_THREE_MODULES',reviewed_source_commit='4f06895ec9473b88b595904b77a453646f52f1e1',
    accepted_kernel_baseline='c1aaa0a00c0c943cec4b2753a937023e9884db04',toolchain='leanprover/lean4:v4.34.0',
    tool_hashes=CONTRACT['tool_hashes'],pins=CONTRACT['pins'],sources=sources,dependencies=deps,
    source_roots={m:r['path'].split('/staged/',1)[0]+'/staged' for m,r in CONTRACT['reviewed_sources'].items()},
    dependency_staged_roots=list(dict.fromkeys(r['path'].split('/staged/',1)[0]+'/staged' for r in deps if r['origin']!='ordinary_build')),
    external_boundary_sources=CONTRACT['external_boundary_sources'],engine_files=[row(p) for p in sorted(paths)],
    required_roots=CONTRACT['required_roots'],required_interfaces=CONTRACT['interfaces'],resource_contract=CONTRACT['resources'],
    project_counts={m:dict(imports=81+i,including_target=82+i) for i,m in enumerate(CONTRACT['modules'])},
    execution_order=[[m,s] for m in CONTRACT['modules'] for s in ['compile','resolve','replay','audit']],
    dependency_qualification='Fresh ordinary-CI inputs and authenticated same-run paid/decoder/bridge objects; no historical object or authenticated clean-cache provenance',
    runtime_route='Accepted bounded CI runner/accounting/lease/receipt engine only; no local mode or artifact input')
save(HERE/'ci-spec.json',spec)
print(json.dumps(dict(sources=len(sources),base_project_dependencies=len(deps),external_boundaries=30,engine_files=len(paths))))
