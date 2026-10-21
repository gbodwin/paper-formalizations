"""Finite integration/source/binding assertions only; never launches Lean or CI."""
from pathlib import Path
import ast
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = '5998c2fded319387483c1e42f485d8b02b7277f4'
SCHEDULE = ROOT / 'checkpoints/light-eft-sequential-validation-schedule-20261021'
PROPOSAL = ROOT / 'checkpoints/light-eft-replay-launcher-privileged-correction-20261021'
NAMES = ['light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
         'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
         'light-eft-fair-bit-batch-ci-adapter-20261021']

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def row(rel):
    raw = (ROOT / rel).read_bytes()
    return dict(path=rel, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())

script = (ROOT / 'scripts/KernelCheck.sh').read_bytes()
assert script == (PROPOSAL / 'PROPOSED-KernelCheck.sh').read_bytes()
assert hashlib.sha256(script).hexdigest() == '9a5cb113fd7c4dc223e7f96fba6558ecde076ba533d71e6980b08d62cce5dd70'
old = git('show', BASE + ':.github/workflows/lean.yml').decode()
before = '      - name: Replay every project module through the Lean kernel\n        run: bash scripts/KernelCheck.sh\n'
after = '      - name: Replay every project module through the Lean kernel\n        shell: /bin/bash --noprofile --norc -p -e -o pipefail {0}\n        run: /bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh\n'
assert old.count(before) == 1
assert (ROOT / '.github/workflows/lean.yml').read_text() == old.replace(before, after)
for prior in ['light-eft-replay-launcher-hoist-proposal-20261021', 'light-eft-replay-launcher-privileged-correction-20261021']:
    for p in (ROOT / 'checkpoints' / prior).iterdir():
        assert p.is_file() and p.read_bytes() == git('show', BASE + ':' + str(p.relative_to(ROOT)))
bound = 0
for name in NAMES:
    rel = 'checkpoints/' + name + '/ci-spec.json'
    before_spec = json.loads(git('show', BASE + ':' + rel))
    now = json.loads((ROOT / rel).read_text())
    old_engine = before_spec.pop('engine_files')
    engine = now.pop('engine_files')
    assert before_spec == now
    assert len(engine) == len({r['path'] for r in engine})
    assert {r['path'] for r in engine} == {r['path'] for r in old_engine} | {'scripts/KernelCheck.sh'}
    assert all(r == row(r['path']) for r in engine)
    sources = list(now['sources'].values()) if isinstance(now['sources'], dict) else now['sources']
    for r in [*sources, *now['dependencies'], *engine]:
        observed = row(r['path'])
        assert observed['bytes'] == r['bytes'] and observed['sha256'] == r['sha256']
        bound += 1
old_refresh = git('show', BASE + ':' + str((SCHEDULE / 'refresh_bindings.py').relative_to(ROOT))).decode()
assert (SCHEDULE / 'refresh_bindings.py').read_text() == old_refresh.replace(
    "extra=[R/'.github/workflows/light-eft-fair-bit-focused.yml',H/'workflow_identity.py',H/'acceptance.py']",
    "extra=[R/'.github/workflows/light-eft-fair-bit-focused.yml',R/'scripts/KernelCheck.sh',H/'workflow_identity.py',H/'acceptance.py']")
policy_rel = str((SCHEDULE / 'workflow_identity.py').relative_to(ROOT))
old_ast = ast.parse(git('show', BASE + ':' + policy_rel))
new_ast = ast.parse((ROOT / policy_rel).read_text())
old_functions = {n.name: ast.dump(n, include_attributes=False) for n in old_ast.body if isinstance(n, ast.FunctionDef)}
new_functions = {n.name: ast.dump(n, include_attributes=False) for n in new_ast.body if isinstance(n, ast.FunctionDef)}
assert set(new_functions) == set(old_functions) | {'replay_launch_controls'}
assert all(new_functions[k] == v for k, v in old_functions.items() if k != 'exact_controls')
modules = json.loads((ROOT / 'checkpoints/light-eft-replay-launcher-hoist-proposal-20261021/MODULES.json').read_text())
assert len(modules) == len({r['module'] for r in modules}) == 567
assert not any(b['module'].startswith(a['module'] + '.') for a in modules for b in modules)
for r in modules:
    actual = row(r['source'])
    assert actual['bytes'] == r['bytes'] and actual['sha256'] == r['sha256']
allowed = {'.github/workflows/lean.yml', 'scripts/KernelCheck.sh', policy_rel,
           str((SCHEDULE / 'refresh_bindings.py').relative_to(ROOT)),
           *['checkpoints/' + n + '/ci-spec.json' for n in NAMES]}
prefix = str(HERE.relative_to(ROOT)) + '/'
changes = git('diff', '--name-only', BASE).decode().splitlines() + git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(p in allowed or p.startswith(prefix) for p in changes)
assert {p.name for p in HERE.iterdir()} == {'README.md', 'check_source.py', 'test_controls.py'}
git('diff', '--check', BASE)
print(json.dumps({'status': 'PASS_SOURCE_INTEGRATION_ONLY', 'reviewed_parent': BASE,
                  'module_carriers': 567, 'binding_rows': bound, 'paired_launch_exact': True,
                  'only_engine_fields_changed_in_five_specs': True, 'proofs_resources_jobs_gates_unchanged': True,
                  'native_execution_or_budget_qualification': False}, sort_keys=True))
