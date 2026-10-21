"""Offline correction/binding checks only; no Lean, shell replay, push or CI."""
from pathlib import Path
import difflib
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = 'd3ab441d7698f93248a0011d2ba996219b5a79a2'
BASE = 'd031f60c681650e48b409115adaffd240ec6493a'
PRIOR = HERE.parent / 'light-eft-replay-launcher-hoist-proposal-20261021'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

for p in PRIOR.iterdir():
    assert p.is_file() and p.read_bytes() == git('show', PARENT + ':' + str(p.relative_to(ROOT)))
old = git('show', BASE + ':scripts/KernelCheck.sh').decode()
workflow = git('show', BASE + ':.github/workflows/lean.yml').decode()
assert (ROOT / 'scripts/KernelCheck.sh').read_text() == old
assert (ROOT / '.github/workflows/lean.yml').read_text() == workflow
candidate = (HERE / 'PROPOSED-KernelCheck.sh').read_text()
prior = (PRIOR / 'PROPOSED-KernelCheck.sh').read_text()
body = prior.split("-c '\n", 1)[1][:-2]
prefix = '''#!/bin/bash -p
# Source-only proposal. CI must start its step shell and this script with -p.
# The option must be in process argv at startup, not enabled after function import.
case $- in
  *p*)
    set -euo pipefail
    if [[ -n ${BASH_ENV-} || -n ${ENV-} ]]; then
      printf "%s\\n" "Kernel replay requires absent shell startup hooks" >&2
      exit 2
    fi
    exec lake env /bin/bash --noprofile --norc -p -euo pipefail -c '
'''
suffix = "'\n    ;;\n  *)\n    # Reserved arithmetic syntax cannot resolve to an imported exit/false function.\n    (( 0 ))\n    ;;\nesac\n"
assert candidate == prefix + body + suffix
old_step = '''      - name: Replay every project module through the Lean kernel
        run: bash scripts/KernelCheck.sh
'''
new_step = '''      - name: Replay every project module through the Lean kernel
        shell: /bin/bash --noprofile --norc -p -e -o pipefail {0}
        run: /bin/bash --noprofile --norc -p -e -o pipefail scripts/KernelCheck.sh
'''
assert workflow.count(old_step) == 1
proposed = workflow.replace(old_step, new_step)
assert proposed.replace(new_step, old_step) == workflow
patch = ''
for rel, a, b in [('scripts/KernelCheck.sh', old, candidate), ('.github/workflows/lean.yml', workflow, proposed)]:
    patch += ''.join(difflib.unified_diff(a.splitlines(keepends=True), b.splitlines(keepends=True),
                                        fromfile='a/' + rel, tofile='b/' + rel, n=0))
assert (HERE / 'PROPOSED.patch').read_text() == patch
plan = json.loads((HERE / 'PLAN.json').read_text())
assert plan['trusted_launch']['runner_shell'] == new_step.split('shell: ', 1)[1].splitlines()[0]
assert plan['trusted_launch']['step_body'] == new_step.split('run: ', 1)[1].strip()
assert plan['trusted_launch']['inner_argv'] == ['/bin/bash', '--noprofile', '--norc', '-p', '-euo', 'pipefail', '-c']
assert plan['resources_unchanged'] == dict(full_minutes=120, focused_minutes=120, aggregate_minutes=5,
    native_wall_seconds=90, all_child_admission_CPU_AS_FSIZE_threads_allocator_stack_lifecycle=True, jobs_added=0)
assert not plan['production_source_or_workflow_modified']
rows = json.loads((PRIOR / 'MODULES.json').read_text())
assert len(rows) == len({r['module'] for r in rows}) == 567
assert not any(b['module'].startswith(a['module'] + '.') for a in rows for b in rows)
for row in rows:
    raw = (ROOT / row['source']).read_bytes()
    assert len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256']
bound = 0
for name in ['light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
             'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
             'light-eft-fair-bit-batch-ci-adapter-20261021']:
    rel = 'checkpoints/' + name + '/ci-spec.json'
    raw = (ROOT / rel).read_bytes()
    assert raw == git('show', PARENT + ':' + rel)
    spec = json.loads(raw)
    sources = list(spec['sources'].values()) if isinstance(spec['sources'], dict) else spec['sources']
    for row in [*sources, *spec['dependencies'], *spec['engine_files']]:
        raw = (ROOT / row['path']).read_bytes()
        assert len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256']
        bound += 1
prefix = str(HERE.relative_to(ROOT)) + '/'
changes = git('diff', '--name-only', PARENT).decode().splitlines() + git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(p.startswith(prefix) for p in changes)
assert {p.name for p in HERE.iterdir()} == {'README.md', 'PLAN.json', 'PROPOSED.patch',
                                         'PROPOSED-KernelCheck.sh', 'test_adversarial.py', 'verify_source.py'}
print(json.dumps({'status': 'PASS_SOURCE_CORRECTION_ONLY', 'prior_preserved': PARENT,
                  'bound_modules': len(rows), 'existing_gate_bindings': bound,
                  'candidate_sha256': hashlib.sha256(candidate.encode()).hexdigest(),
                  'production_patch_unapplied': True, 'privileged_startup_required_at_all_three_entries': True,
                  'new_job_or_limit': False, 'native_execution_acceptance': False}, sort_keys=True))
