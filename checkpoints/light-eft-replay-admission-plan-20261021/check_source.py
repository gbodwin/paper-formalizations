"""Additive proposal/placement/binding checks only. Never executes admission."""
from pathlib import Path
import ast
import difflib
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = '0747b30af2bafcc57ae2ab89289af59d670c8068'
REL = str(HERE.relative_to(ROOT)) + '/replay_preflight.py'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

old = git('show', BASE + ':scripts/KernelCheck.sh').decode()
workflow = git('show', BASE + ':.github/workflows/lean.yml').decode()
assert (ROOT / 'scripts/KernelCheck.sh').read_text() == old
assert (ROOT / '.github/workflows/lean.yml').read_text() == workflow
body = old.split("-c '\n", 1)[1].split("'\n    ;;", 1)[0]
loop = '/usr/bin/python3 -I -B ' + REL + ' verify "$-" "$BASH_VERSION"\n' + body
candidate = old.replace('exec lake env /bin/bash --noprofile --norc -p -euo pipefail -c \'\n' + body,
                        'exec /usr/bin/python3 -I -B ' + REL + ' before-lake /bin/bash --noprofile --norc -p -euo pipefail -c \'\n' + loop)
assert (HERE / 'PROPOSED-KernelCheck.sh').read_text() == candidate
env = '''        env:
          LIGHTEFT_JOB_WORKFLOW_REF: ${{ job.workflow_ref }}
          LIGHTEFT_JOB_WORKFLOW_SHA: ${{ job.workflow_sha }}
          LIGHTEFT_JOB_WORKFLOW_PATH: ${{ job.workflow_file_path }}
          LIGHTEFT_JOB_WORKFLOW_REPOSITORY: ${{ job.workflow_repository }}
'''
before = '''      - name: Replay every project module through the Lean kernel
        shell: /bin/bash --noprofile --norc -p -e -o pipefail {0}
        run: /bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh
'''
bootstrap = '''      - name: Observe replay launcher admission on this runner
        shell: /usr/bin/python3 -I -B {0}
''' + env + '''        run: |
          import runpy, sys
          sys.argv = [''' + repr(REL) + ''', 'bootstrap']
          runpy.run_path(''' + repr(REL) + ''', run_name='__main__')
'''
global_step = '      - name: Replay every project module through the Lean kernel\n' + env + '''        shell: /bin/bash --noprofile --norc -p -e -o pipefail {0}
        run: /bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh
'''
assert workflow.count(before) == 1
proposed = workflow.replace(before, bootstrap + global_step)
needle = '            ${{ runner.temp }}/light-eft-summary-${{ github.run_id }}-${{ github.run_attempt }}\n'
proposed = proposed.replace(needle, needle + '            ${{ runner.temp }}/light-eft-replay-admission-${{ github.run_id }}-${{ github.run_attempt }}\n')
assert proposed.index('runpy.run_path') > proposed.index('Verify canonical actual-output corollary after three context replays')
assert proposed.index('runpy.run_path') < proposed.index('      - name: Replay every project module through the Lean kernel')
patch = ''
for rel, a, b in [('scripts/KernelCheck.sh', old, candidate), ('.github/workflows/lean.yml', workflow, proposed)]:
    patch += ''.join(difflib.unified_diff(a.splitlines(keepends=True), b.splitlines(keepends=True), fromfile='a/' + rel, tofile='b/' + rel, n=0))
assert (HERE / 'PROPOSED.patch').read_text() == patch
helper = ast.parse((HERE / 'replay_preflight.py').read_text())
constants = {n.targets[0].id: ast.literal_eval(n.value) for n in helper.body
             if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
             and n.targets[0].id in ['SCRIPT_SHA', 'LOOP_SHA', 'PROJECTIONS', 'ABSENT']}
assert constants['SCRIPT_SHA'] == hashlib.sha256(candidate.encode()).hexdigest()
assert constants['LOOP_SHA'] == hashlib.sha256(loop.encode()).hexdigest()
assert len(constants['PROJECTIONS']) == 5 and set(constants['ABSENT']) == {'SHELLOPTS', 'BASHOPTS', 'CDPATH', 'GLOBIGNORE', 'BASH_ENV', 'ENV'}
for name in ['before_lake', 'enter']:
    function = next(n for n in helper.body if isinstance(n, ast.FunctionDef) and n.name == name)
    handoff = next(i for i, n in enumerate(function.body) if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call)
                   and isinstance(n.value.func, ast.Attribute) and n.value.func.attr == 'execv')
    assert any(isinstance(n, ast.Expr) and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Attribute)
               and n.value.func.attr == 'setitimer' and isinstance(n.value.args[-1], ast.Constant) and n.value.args[-1].value == 0
               for n in function.body[:handoff])
bound = 0
for name in ['light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
             'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
             'light-eft-fair-bit-batch-ci-adapter-20261021']:
    rel = 'checkpoints/' + name + '/ci-spec.json';raw = (ROOT / rel).read_bytes()
    assert raw == git('show', BASE + ':' + rel)
    spec = json.loads(raw)
    assert REL not in {r['path'] for r in spec['engine_files']}  # Current candidate is deliberately not admission authority.
    sources = list(spec['sources'].values()) if isinstance(spec['sources'], dict) else spec['sources']
    for r in [*sources, *spec['dependencies'], *spec['engine_files']]:
        raw = (ROOT / r['path']).read_bytes()
        assert len(raw) == r['bytes'] and hashlib.sha256(raw).hexdigest() == r['sha256'];bound += 1
modules = json.loads((ROOT / 'checkpoints/light-eft-replay-launcher-hoist-proposal-20261021/MODULES.json').read_text())
assert len(modules) == len({r['module'] for r in modules}) == 567
for r in modules:
    raw = (ROOT / r['source']).read_bytes();assert len(raw) == r['bytes'] and hashlib.sha256(raw).hexdigest() == r['sha256']
plan = json.loads((HERE / 'PLAN.json').read_text())
assert plan['production_unchanged'] and plan['base'] == BASE and plan['Lake_setups'] == 1
assert plan['job_envelopes_minutes'] == [120, 120, 5] and plan['existing_child_wall_seconds'] == 90
assert [x['name'] for x in plan['phases']] == ['bootstrap', 'before-lake', 'enter', 'verify']
prefix = str(HERE.relative_to(ROOT)) + '/'
changed = git('diff', '--name-only', BASE).decode().splitlines() + git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(p.startswith(prefix) for p in changed)
assert {p.name for p in HERE.iterdir()} == {'README.md', 'PLAN.json', 'PROPOSED.patch', 'PROPOSED-KernelCheck.sh', 'replay_preflight.py', 'test_models.py', 'check_source.py'}
git('diff', '--check', BASE)
print(json.dumps({'status': 'PASS_ADDITIVE_ADMISSION_PROPOSAL_ONLY', 'existing_bindings': bound,
                  'module_carriers': 567, 'Lake_setups': 1, 'ordinary_build_and_current_gates_unchanged': True,
                  'placement': 'only immediately before new global launcher',
                  'hosted_runner_observations_or_execution_authority': False}, sort_keys=True))
