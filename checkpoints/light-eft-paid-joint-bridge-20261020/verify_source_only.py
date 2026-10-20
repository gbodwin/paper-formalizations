"""Finite source/byte checks; does not elaborate Lean or exercise a runtime gate."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = '2beb9958f70b975baeb58c9f46caaa24dfe79795'
PREFIX = HERE.relative_to(ROOT).as_posix() + '/'

def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])

expected = {
    'README.md', 'PROOF-ARGUMENT.md', 'UNRESOLVED.md', 'SOURCE-BINDINGS.json',
    'verify_source_only.py',
    'staged/LightEFTPaidJointBridgeStage/SuppliedResponseJointBridge.lean',
}
assert {p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file()} == expected
changes = git('diff', '--name-status', BASE, '--').decode().splitlines()
assert all(line.startswith('A\t' + PREFIX) for line in changes), changes
other = git('ls-files', '--others', '--exclude-standard').decode().splitlines()
assert all(path.startswith(PREFIX) for path in other), other
git('diff', '--check', BASE, '--')

bindings = json.loads((HERE / 'SOURCE-BINDINGS.json').read_text())
assert bindings['accepted_base'] == BASE
assert len(bindings['source_inputs']) == 13
for row in bindings['source_inputs']:
    old = git('show', f"{BASE}:{row['path']}")
    current = (ROOT / row['path']).read_bytes()
    assert old == current
    assert (len(current), hashlib.sha256(current).hexdigest()) == (row['bytes'], row['sha256'])

target = HERE / 'staged/LightEFTPaidJointBridgeStage/SuppliedResponseJointBridge.lean'
src = target.read_text()
assert re.findall(r'^import (.+)$', src, re.M) == [
    'LightEFTPaidSamplingStage.PaidFlagSampleComposition',
    'LightEFTJointFlagSamplingStage.JointAssignmentLaw',
    'LightEFTSpanners.StoredFlagSampleEncoding',
]
assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial|implemented_by|extern|run_tac)\b|^\s*#', src, re.M)
assert len(re.findall(r'^theorem ', src, re.M)) == 12
assert len(re.findall(r'^noncomputable def ', src, re.M)) == 5
assert not re.search(r'^def |^inductive |^opaque ', src, re.M)
assert all(line == line.rstrip() and '\t' not in line for line in src.splitlines())
assert src.endswith('\n')

compilers = []
for p in Path('/proc').iterdir():
    if p.name.isdecimal():
        try:
            comm = (p / 'comm').read_text().strip()
            if comm in {'lean', 'lake', 'leanc', 'LeanChecker'}:
                compilers.append({'pid': int(p.name), 'comm': comm})
        except OSError:
            pass
assert not compilers, compilers

print(json.dumps({
    'kind': 'source/byte checks only; not Lean elaboration or proof validation',
    'base': BASE,
    'only_new_checkpoint_files': True,
    'accepted_source_bindings_match': len(bindings['source_inputs']),
    'all_other_tracked_files_preserved': True,
    'direct_imports': 3, 'new_theorems_uncompiled': 12,
    'mathematical_noncomputable_definitions': 5,
    'no_admissions_or_execution_commands_in_target': True,
    'target_bytes': target.stat().st_size,
    'target_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
    'local_compiler_processes_at_observation': compilers,
    'Lean_or_supervisor_launched': False,
    'CI_or_push_launched': False,
    'independent_review': 'pending parent review; author source inspection is separate',
}, indent=2))
