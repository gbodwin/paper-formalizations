"""Offline proposal/source/patch binding only. No native process or CI route."""
from pathlib import Path
import difflib
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = 'd031f60c681650e48b409115adaffd240ec6493a'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

old = git('show', BASE + ':scripts/KernelCheck.sh').decode()
candidate = (HERE / 'PROPOSED-KernelCheck.sh').read_text()
assert (ROOT / 'scripts/KernelCheck.sh').read_text() == old
expected_body = '# Sequential replay avoids' + old.split('# Sequential replay avoids', 1)[1]
expected_body = expected_body.replace('    lake env leanchecker -v "$module"',
                                     '    hash -r\n    command leanchecker -v "$module"')
assert candidate.split("-c '\n", 1)[1] == expected_body + "'\n"
assert candidate.count('exec lake env "$BASH"') == 1
assert '[[ -n ${BASH_ENV-} || -n ${ENV-} ]]' in candidate and 'exit 2' in candidate
patch = ''.join(difflib.unified_diff(old.splitlines(keepends=True), candidate.splitlines(keepends=True),
                                   fromfile='a/scripts/KernelCheck.sh', tofile='b/scripts/KernelCheck.sh', n=0))
assert (HERE / 'PROPOSED.patch').read_text() == patch

plan = json.loads((HERE / 'PLAN.json').read_text())
assert plan['base'] == BASE and plan['checkpoint_is_additive_only']
assert plan['unchanged']['job_count'] == 3 and plan['unchanged']['full_job_minutes'] == 120
assert plan['unchanged']['focused_job_minutes'] == 120 and plan['unchanged']['native_wall_seconds'] == 90
assert not plan['limits_and_coverage_changes'] and plan['no_result_cache'] and plan['no_import_or_kernel_scan_cache']
rows = json.loads((HERE / 'MODULES.json').read_text())
assert len(rows) == len({r['module'] for r in rows}) == 567
assert not any(b['module'].startswith(a['module'] + '.') for a in rows for b in rows)
for row in rows:
    p = Path(row['source'])
    assert not p.is_absolute() and '..' not in p.parts and not (ROOT / p).is_symlink()
    raw = (ROOT / p).read_bytes()
    assert len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256']
    assert raw == git('show', BASE + ':' + str(p))

spec_names = ['light-eft-paid-focused-adapter-20261020', 'light-eft-joint-flag-ci-extension-revision-20261019',
              'light-eft-canonical-output-adapter-20261020', 'light-eft-paid-joint-bridge-ci-adapter-20261020',
              'light-eft-fair-bit-batch-ci-adapter-20261021']
bound = 0
engine_bound = 0
for name in spec_names:
    rel = 'checkpoints/' + name + '/ci-spec.json'
    raw = (ROOT / rel).read_bytes()
    assert raw == git('show', BASE + ':' + rel)
    spec = json.loads(raw)
    sources = spec['sources']
    if isinstance(sources, dict):
        sources = list(sources.values())
    for row in [*sources, *spec['dependencies'], *spec['engine_files']]:
        p = ROOT / row['path']
        raw = p.read_bytes()
        assert len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256']
        bound += 1
    engine_bound += len(spec['engine_files'])
prefix = str(HERE.relative_to(ROOT)) + '/'
changed = git('diff', '--name-only', BASE).decode().splitlines()
untracked = git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(p.startswith(prefix) for p in changed + untracked)
assert {p.name for p in HERE.iterdir()} == {'README.md', 'PLAN.json', 'MODULES.json', 'PROPOSED.patch',
                                         'PROPOSED-KernelCheck.sh', 'test_models.py', 'verify_source.py'}
print(json.dumps({'status': 'PASS_SOURCE_PROPOSAL_ONLY', 'base': BASE,
                  'modules': len(rows), 'all_gate_bindings': bound, 'gate_engine_bindings': engine_bound,
                  'proposed_script_sha256': hashlib.sha256(candidate.encode()).hexdigest(),
                  'production_files_unchanged': True, 'new_job_or_limit': False,
                  'native_runtime_or_kernel_acceptance': False}, sort_keys=True))
