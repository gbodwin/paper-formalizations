"""Finite static source assertions; NOT EXECUTED in this author unit."""
from pathlib import Path
import ast, hashlib, json, subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = '5cd7f7eb688b519b84d71b75c705b1381be08165'
GATE = 'checkpoints/light-eft-canonical-output-adapter-20261020/ci_gate.py'
NAMES = ['light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
         'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
         'light-eft-fair-bit-batch-ci-adapter-20261021']

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def dump(node):
    return ast.dump(node, include_attributes=False)

gate = (ROOT / GATE).read_bytes()
assert hashlib.sha256(gate).hexdigest() == 'f825f46389874775b22812afc1f3764a63997656a2df016143fe2bfa69cfb5dc'
old = {n.name: n for n in ast.parse(git('show', BASE + ':' + GATE)).body if isinstance(n, ast.FunctionDef)}
new = {n.name: n for n in ast.parse(gate).body if isinstance(n, ast.FunctionDef)}
assert set(new) == set(old)
assert all(dump(new[k]) == dump(old[k]) for k in old if k not in ['context_type', 'run_stage'])
factory = new['context_type']
assert [a.arg for a in factory.args.kwonlyargs] == ['admission_module']
assert isinstance(factory.args.kw_defaults[0], ast.Constant) and factory.args.kw_defaults[0].value is None
text = gate.decode()
for fragment in [
    'canonical_context=admission_module is None',
    "expected_identity=tuple((TARGET,stage) for stage in STAGES)",
    "expected_identity=((admission_module,'replay'),)",
    'frozen_plans=tuple(encoded(p) for p in commands)',
    'tuple(encoded(p) for p in plans)==frozen_plans',
    "if canonical_context and expected['stage'] in ['replay','audit']:",
    "if canonical_context and expected['stage']=='resolve'",
    'completed_prerequisite(prior,json.loads(frozen_plans[1])',
    "admission_authority=tuple(zip(admissions,tuple(CONTRACT['replay_order']),strict=True))",
    'for entry,module in admission_authority if entry is a',
    'admission_module=module']:
    assert fragment in text
assert "if p['module']==TARGET" not in text
assert text.count('checked_plan(self.plans,len(self.seen),p)') == 4

regular = recursive = 0
for name in NAMES:
    rel = 'checkpoints/' + name + '/ci-spec.json'
    before = json.loads(git('show', BASE + ':' + rel))
    after = json.loads((ROOT / rel).read_text())
    old_engine, engine = before.pop('engine_files'), after.pop('engine_files')
    assert before == after
    assert len(engine) == len({r['path'] for r in engine})
    assert {r['path'] for r in engine} == {r['path'] for r in old_engine}
    for r in engine:
        raw = (ROOT / r['path']).read_bytes()
        assert len(raw) == r['bytes'] and hashlib.sha256(raw).hexdigest() == r['sha256']
    sources = after['sources']
    sources = list(sources.values()) if isinstance(sources, dict) else sources
    regular += len(sources) + len(after['dependencies']) + len(engine)
    def walk(value):
        global recursive
        if isinstance(value, dict):
            if isinstance(value.get('path'), str) and 'sha256' in value and 'bytes' in value:
                raw = (ROOT / value['path']).read_bytes()
                assert len(raw) == value['bytes'] and hashlib.sha256(raw).hexdigest() == value['sha256']
                recursive += 1
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)
    walk(json.loads((ROOT / rel).read_text()))
assert regular == 1034 and recursive == 1041
engine = 'checkpoints/light-eft-canonical-output-adapter-20261020/'
for rel in [engine + n for n in ['canonical_fixture.py', 'ci_policy.py', 'ci_receipts.py',
        'ci_admission.py', 'ci_admission_receipts.py', 'child_runner.py', 'pilot_child.py',
        'scope.py', 'contracts.py', 'ci_accounting.py', 'ci_inventory.py', 'ci_lease.py',
        'output_guards.py', 'ci_handoff.py', 'ci_handoff_contract.py', 'staged/CanonicalOutputAudit.lean']] + [
        '.github/workflows/lean.yml', '.github/workflows/light-eft-fair-bit-focused.yml',
        'scripts/KernelCheck.sh', 'checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py',
        'checkpoints/light-eft-canonical-key-cache-integration-20261022/staged/CanonicalKeyEquivalenceFixtures.lean',
        'checkpoints/light-eft-canonical-key-cache-integration-20261022/staged/ResolveAfterCanonicalEquivalence.lean']:
    assert (ROOT / rel).read_bytes() == git('show', BASE + ':' + rel)
allowed = {GATE, *['checkpoints/' + name + '/ci-spec.json' for name in NAMES]}
prefix = str(HERE.relative_to(ROOT)) + '/'
changed = git('diff', '--name-only', BASE).decode().splitlines() + git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(p in allowed or p.startswith(prefix) for p in changed)
git('diff', '--check', BASE)
print(json.dumps(dict(status='STATIC_SOURCE_ONLY', regular_rows=regular, recursive_rows=recursive,
                      runtime_or_model_qualification=False)))
