"""Offline exact byte-binding refresh; no compiler, queue mutation or CI launch."""
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PAID = ROOT / 'checkpoints/light-eft-paid-focused-adapter-20261020'
DECODER = ROOT / 'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'
ENGINE = ROOT / 'checkpoints/light-eft-canonical-output-adapter-20261020'
PLAN = json.loads((ROOT / 'checkpoints/light-eft-paid-joint-bridge-ci-plan-20261020/PLAN.json').read_text())

def row(path, **extra):
    raw = path.read_bytes()
    return dict(path=str(path.relative_to(ROOT)), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest(), **extra)

def save(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')

workflow = ROOT / '.github/workflows/lean.yml'
for path in [PAID / 'ci-spec.json', DECODER / 'ci-spec.json', ENGINE / 'ci-spec.json']:
    data = json.loads(path.read_text())
    for i, record in enumerate(data['engine_files']):
        if record['path'] in ['.github/workflows/lean.yml', 'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019/ci-spec.json']:
            data['engine_files'][i] = row(ROOT / record['path'])
    save(path, data)
old_specs = [json.loads((p / 'ci-spec.json').read_text()) for p in [PAID, DECODER, ENGINE]]
paths = {p for p in HERE.glob('*.py')}
for folder, data in zip([PAID, DECODER, ENGINE], old_specs, strict=True):
    paths.add(folder / 'ci-spec.json')
    for record in data['engine_files']:
        paths.add(ROOT / record['path'])
    values = data['sources'] if isinstance(data['sources'], list) else data['sources'].values()
    paths.update(ROOT / record['path'] for record in values)
paths.update([workflow, ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain'])
sources = [row(ROOT / PLAN['target_source']['path'], role='bridge'),
           row(HERE / 'staged/BridgeAudit.lean', role='audit'),
           row(HERE / 'staged/ResolveBridgeTarget.lean', role='resolver')]
deps = [{k: record[k] for k in ['module', 'path', 'bytes', 'sha256', 'origin']} for record in PLAN['dependencies']]
spec = dict(scope='SUPPLIED_RESPONSE_OUTPUT_TO_IDEAL_JOINT_DECODER_EXACT_SINGLETON',
    reviewed_source_commit=PLAN['reviewed_source_commit'], source_plan_commit='eab618b2e043bd5509e814357c1b8c9305ac74cd',
    toolchain=PLAN['toolchain'], tool_hashes=PLAN['tool_hashes'], pins=PLAN['pins'],
    staged_root='checkpoints/light-eft-paid-joint-bridge-20261020/staged', sources=sources,
    dependency_staged_roots=list(dict.fromkeys(record['path'].split('/staged/',1)[0]+'/staged' for record in deps if record['origin']!='ordinary_build')),
    dependencies=deps, external_boundary_sources=PLAN['external_boundary_sources'],
    engine_files=[row(p) for p in sorted(paths)], project_imports=80, project_modules_including_target=81,
    required_theorem_roots=PLAN['audit']['required_theorem_roots'],
    required_interfaces=PLAN['audit']['required_reachable_interfaces'],
    resource_contract=PLAN['resources'], execution_order=['compile', 'resolve', 'replay', 'audit'],
    dependency_qualification='Fresh ordinary-CI build and authenticated same-run paid/decoder outputs; no historical preservation or authenticated clean-cache provenance',
    runtime_route='Accepted bounded CI child runner/accounting/lease/receipt engine only; no local mode, dispatch or artifact download')
save(HERE / 'ci-spec.json', spec)
print(json.dumps(dict(sources=len(sources), dependencies=len(deps), engine_files=len(paths))))
