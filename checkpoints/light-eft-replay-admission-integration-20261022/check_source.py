"""Finite source integration assertions only; never imports or runs admission."""
from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = 'adeaa012e3dd6ac27e96559088636f366e80fbf4'
PLAN = ROOT / 'checkpoints/light-eft-replay-admission-plan-20261021'
SCHEDULE = ROOT / 'checkpoints/light-eft-sequential-validation-schedule-20261021'
HELPER = str((PLAN / 'replay_preflight.py').relative_to(ROOT))
NAMES = ['light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
         'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
         'light-eft-fair-bit-batch-ci-adapter-20261021']

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def row(path):
    raw = (ROOT / path).read_bytes()
    return dict(path=path, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())

def apply_zero_patch(old, target, patch):
    section = next(x for x in patch.split('--- a/')[1:] if x.splitlines()[0] == target)
    lines = section.splitlines(keepends=True)[2:]
    original = old.splitlines(keepends=True)
    out, cursor, i = [], 0, 0
    while i < len(lines):
        match = re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@\n', lines[i])
        assert match
        start, count = int(match[1]), int(match[2] or 1)
        index = start if count == 0 else start - 1
        out.extend(original[cursor:index]);cursor = index;i += 1
        removed = added = 0
        while i < len(lines) and not lines[i].startswith('@@ '):
            line = lines[i]
            if line.startswith('-'):
                assert original[cursor] == line[1:];cursor += 1;removed += 1
            elif line.startswith('+'):
                out.append(line[1:]);added += 1
            else:
                raise AssertionError('Only reviewed zero-context edits allowed')
            i += 1
        assert removed == count and added == int(match[4] or 1)
    return ''.join(out + original[cursor:])

for prior in ['light-eft-replay-launcher-hoist-proposal-20261021',
              'light-eft-replay-launcher-privileged-correction-20261021', 'light-eft-replay-admission-plan-20261021']:
    for path in (ROOT / 'checkpoints' / prior).iterdir():
        assert path.is_file() and path.read_bytes() == git('show', BASE + ':' + str(path.relative_to(ROOT)))
patch = (PLAN / 'PROPOSED.patch').read_text()
for target in ['scripts/KernelCheck.sh', '.github/workflows/lean.yml']:
    expected = apply_zero_patch(git('show', BASE + ':' + target).decode(), target, patch)
    assert (ROOT / target).read_text() == expected
script = (ROOT / 'scripts/KernelCheck.sh').read_bytes()
helper = (ROOT / HELPER).read_bytes()
assert script == (PLAN / 'PROPOSED-KernelCheck.sh').read_bytes()
assert row(HELPER)['sha256'] == '72f33cd3676552f902cc7361ae805186971bbdf07e1f3fcc13a45a81b3797425'
assert hashlib.sha256(script).hexdigest() == 'b7dac23e6300e3c34d6192887f52d6f780b2bef9720f43b94d4c0f1b3116d77d'
loop = script.split(b"-c '\n", 1)[1].split(b"'\n    ;;", 1)[0]
assert hashlib.sha256(loop).hexdigest() == '53717997a6a67054021e6b82a61113676e62b2f2ed134868ffd622eb86874bbb'
bound = 0
for name in NAMES:
    path = 'checkpoints/' + name + '/ci-spec.json'
    before = json.loads(git('show', BASE + ':' + path));now = json.loads((ROOT / path).read_text())
    old_engine, engine = before.pop('engine_files'), now.pop('engine_files')
    assert before == now
    assert len(engine) == len({r['path'] for r in engine})
    assert {r['path'] for r in engine} == {r['path'] for r in old_engine} | {HELPER}
    assert all(r == row(r['path']) for r in engine)
    sources = list(now['sources'].values()) if isinstance(now['sources'], dict) else now['sources']
    for r in [*sources, *now['dependencies'], *engine]:
        actual = row(r['path']);assert actual['bytes'] == r['bytes'] and actual['sha256'] == r['sha256'];bound += 1
refresh_path = str((SCHEDULE / 'refresh_bindings.py').relative_to(ROOT))
before = git('show', BASE + ':' + refresh_path).decode()
assert (ROOT / refresh_path).read_text() == before.replace(
    "extra=[R/'.github/workflows/light-eft-fair-bit-focused.yml',R/'scripts/KernelCheck.sh',H/'workflow_identity.py',H/'acceptance.py']",
    "extra=[R/'.github/workflows/light-eft-fair-bit-focused.yml',R/'scripts/KernelCheck.sh',\n       R/'" + HELPER + "',H/'workflow_identity.py',H/'acceptance.py']")
policy = str((SCHEDULE / 'workflow_identity.py').relative_to(ROOT))
def functions(raw):
    return {n.name: ast.dump(n, include_attributes=False) for n in ast.parse(raw).body if isinstance(n, ast.FunctionDef)}
a, b = functions(git('show', BASE + ':' + policy)), functions((ROOT / policy).read_bytes())
assert set(a) == set(b) and all(a[k] == b[k] for k in a if k not in ['exact_controls', 'replay_launch_controls'])
modules = json.loads((ROOT / 'checkpoints/light-eft-replay-launcher-hoist-proposal-20261021/MODULES.json').read_text())
assert len(modules) == len({r['module'] for r in modules}) == 567
assert not any(b['module'].startswith(a['module'] + '.') for a in modules for b in modules)
for r in modules:
    actual = row(r['source']);assert actual['bytes'] == r['bytes'] and actual['sha256'] == r['sha256']
allowed = {'scripts/KernelCheck.sh', '.github/workflows/lean.yml', refresh_path, policy,
           *['checkpoints/' + n + '/ci-spec.json' for n in NAMES]}
prefix = str(HERE.relative_to(ROOT)) + '/'
changed = git('diff', '--name-only', BASE).decode().splitlines() + git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(p in allowed or p.startswith(prefix) for p in changed)
assert {p.name for p in HERE.iterdir()} == {'README.md', 'check_source.py', 'test_controls.py'}
git('diff', '--check', BASE)
print(json.dumps({'status': 'PASS_REVIEWED_ADMISSION_INTEGRATION_SOURCE_ONLY', 'reviewed_base': BASE,
                  'binding_rows': bound, 'module_carriers': 567, 'helper_script_loop_exact': True,
                  'prior_sources_and_proof_resource_lifecycle_status_gates_preserved': True,
                  'actual_admission_native_or_budget_qualification': False}, sort_keys=True))
