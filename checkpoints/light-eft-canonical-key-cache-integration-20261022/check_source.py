"""Finite source assertions only; NOT EXECUTED in this source-only author unit."""
from pathlib import Path
import ast, hashlib, json, subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = 'a60f82f25daff94c0818613d2146a5fd6c33727b'
ENGINE = 'checkpoints/light-eft-canonical-output-adapter-20261020/'
PROPOSAL = ROOT / 'checkpoints/light-eft-canonical-key-cache-proposal-20261022'
HELPER = ENGINE + 'canonical_fixture.py'
NAMES = ['light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
         'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
         'light-eft-fair-bit-batch-ci-adapter-20261021']

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def row(path):
    raw = (ROOT / path).read_bytes()
    return dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())

def functions(raw):
    return {n.name: n for n in ast.parse(raw).body if isinstance(n, ast.FunctionDef)}

def dump(node):
    return ast.dump(node, include_attributes=False)

for p in PROPOSAL.iterdir():
    assert p.read_bytes() == git('show', BASE + ':' + str(p.relative_to(ROOT)))
for actual, proposed in [
    (ROOT / ENGINE / 'staged/CanonicalOutputAudit.lean', PROPOSAL / 'PROPOSED-CanonicalOutputAudit.lean'),
    (HERE / 'staged/CanonicalKeyEquivalenceFixtures.lean', PROPOSAL / 'PROPOSED-CanonicalKeyEquivalenceFixtures.lean'),
    (HERE / 'staged/ResolveAfterCanonicalEquivalence.lean', PROPOSAL / 'PROPOSED-ResolveAfterCanonicalEquivalence.lean')]:
    assert actual.read_bytes() == proposed.read_bytes()
assert row(HELPER)['sha256'] == 'afec43578ea586a28b814a2b245d3ee1574ef1b3f099fee4c0d81f1c6cb4e52d'

regular = recursive = 0
for name in NAMES:
    path = 'checkpoints/' + name + '/ci-spec.json'
    before = json.loads(git('show', BASE + ':' + path))
    now = json.loads((ROOT / path).read_text())
    old_engine, engine = before.pop('engine_files'), now.pop('engine_files')
    assert len(engine) == len({r['path'] for r in engine})
    assert {r['path'] for r in engine} == {r['path'] for r in old_engine} | {HELPER}
    if name == 'light-eft-canonical-output-adapter-20261020':
        old_sources, sources = before.pop('sources'), now.pop('sources')
        assert sources['source'] == old_sources['source']
        assert sources['original_resolver'] == old_sources['resolver']
        assert set(sources) == {'source', 'audit', 'resolver', 'key_fixture', 'original_resolver'}
        assert sources['audit'] == row(ENGINE + 'staged/CanonicalOutputAudit.lean')
        assert sources['resolver'] == row(str((HERE / 'staged/ResolveAfterCanonicalEquivalence.lean').relative_to(ROOT)))
        assert sources['key_fixture'] == row(str((HERE / 'staged/CanonicalKeyEquivalenceFixtures.lean').relative_to(ROOT)))
    else:
        sources = now['sources']
    assert before == now
    src = list(sources.values()) if isinstance(sources, dict) else sources
    # All regular rows, and every nested object-admission row, are retained.
    for r in [*src, *now['dependencies'], *engine]:
        assert all(row(r['path'])[k] == r[k] for k in ['bytes', 'sha256'])
        regular += 1
    full = json.loads((ROOT / path).read_text())
    def walk(value):
        global recursive
        if isinstance(value, dict):
            if isinstance(value.get('path'), str) and 'bytes' in value and 'sha256' in value:
                assert all(row(value['path'])[k] == value[k] for k in ['bytes', 'sha256'])
                recursive += 1
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)
    walk(full)
assert regular == 1034 and recursive == 1041

for rel in [ENGINE + n for n in ['child_runner.py', 'pilot_child.py', 'scope.py', 'contracts.py',
        'ci_lease.py', 'ci_accounting.py', 'ci_admission.py', 'ci_admission_receipts.py',
        'output_guards.py', 'ci_handoff.py', 'ci_handoff_contract.py', 'ci_inventory.py']] + [
        '.github/workflows/lean.yml', '.github/workflows/light-eft-fair-bit-focused.yml', 'scripts/KernelCheck.sh',
        'checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py',
        'scripts/LightEFTProcessLifecycle.py']:
    assert (ROOT / rel).read_bytes() == git('show', BASE + ':' + rel)
for name, changed in [('ci_gate.py', {'context_type', 'run_stage'}), ('ci_policy.py', {'plans'})]:
    old = functions(git('show', BASE + ':' + ENGINE + name))
    new = functions((ROOT / ENGINE / name).read_bytes())
    assert set(old) == set(new)
    assert all(dump(old[k]) == dump(new[k]) for k in old if k not in changed)
old = functions(git('show', BASE + ':' + ENGINE + 'ci_receipts.py'))['verify_receipts']
new = functions((ROOT / ENGINE / 'ci_receipts.py').read_bytes())['verify_receipts']
assert [dump(n) for n in old.body[:-1]] == [dump(n) for n in new.body[:-2]]
assert dump(old.body[-1]) == dump(new.body[-1])
assert [a.arg for a in new.args.args] == [a.arg for a in old.args.args] + ['expected_identity']
assert "expected_identity=identity" in (ROOT / ENGINE / 'ci_gate.py').read_text()
modules = json.loads((ROOT / 'checkpoints/light-eft-replay-launcher-hoist-proposal-20261021/MODULES.json').read_text())
assert len(modules) == len({r['module'] for r in modules}) == 567
for r in modules:
    assert all(row(r['source'])[k] == r[k] for k in ['bytes', 'sha256'])
allowed = {ENGINE + n for n in ['ci_gate.py', 'ci_policy.py', 'ci_receipts.py', 'canonical_fixture.py',
                               'staged/CanonicalOutputAudit.lean']}
allowed |= {'checkpoints/' + n + '/ci-spec.json' for n in NAMES}
prefix = str(HERE.relative_to(ROOT)) + '/'
changed = git('diff', '--name-only', BASE).decode().splitlines() + git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(p in allowed or p.startswith(prefix) for p in changed)
git('diff', '--check', BASE)
print(json.dumps(dict(status='SOURCE_ASSERTIONS_ONLY', regular_rows=regular, nested_object_admission_rows=7,
                      recursive_rows=recursive, model_or_native_qualification=False)))
