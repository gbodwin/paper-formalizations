"""Offline source inventory checks. Never imports or starts a Lean/runtime gate."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = 'c1aaa0a00c0c943cec4b2753a937023e9884db04'
PREFIX = str(HERE.relative_to(ROOT)) + '/'
inventory = json.loads((HERE / 'SOURCE-BINDINGS.json').read_text())
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git', '-C', str(ROOT), *args])

assert inventory['base_commit'] == BASE
assert inventory['verification_status'] == 'UNELABORATED_SOURCE_ONLY'
assert len(inventory['project_imports']) == 81
assert len({r['module'] for r in inventory['project_imports']}) == 81
for row in [*inventory['checkpoint_files'], *inventory['project_imports'],
            inventory['accepted_spec'], *inventory['primary_sources']]:
    path = Path(row['path'])
    raw = (path if path.is_absolute() else ROOT / path).read_bytes()
    assert (len(raw), sha(raw)) == (row['bytes'], row['sha256']), row['path']
for row in [*inventory['project_imports'], inventory['accepted_spec']]:
    assert git('show', BASE + ':' + row['path']) == (ROOT / row['path']).read_bytes()
for row in inventory['primary_sources']:
    raw = Path(row['path']).read_text()
    assert all(marker in raw for marker in row['statement_markers']), row['path']
    if row['package'] == 'mathlib':
        package = Path(inventory['mathlib']['local_root'])
        assert subprocess.check_output(['git', '-C', str(package), 'rev-parse', 'HEAD'],
                                       text=True).strip() == inventory['mathlib']['rev']
        assert subprocess.check_output(['git', '-C', str(package), 'show',
            inventory['mathlib']['rev'] + ':' + row['package_path']]) == Path(row['path']).read_bytes()

expected = {PREFIX + p for p in inventory['checkpoint_relative_files']}
changes = git('diff', '--name-status', BASE).decode().splitlines()
changed = set()
for line in changes:
    status, path = line.split('\t')
    assert status == 'A' and path in expected, line
    changed.add(path)
untracked = set(git('ls-files', '--others', '--exclude-standard').decode().splitlines())
assert changed | untracked == expected and not changed & untracked
raw = (HERE / 'staged/LightEFTFlatTapeStage/FlatTapeLaw.lean').read_text()
assert re.findall(r'^import (.+)$', raw, re.M) == [
    'LightEFTPaidJointBridgeStage.SuppliedResponseJointBridge']
assert not re.search(r'\b(sorry|admit)\b', raw)
assert not re.search(r'^\s*(axiom|unsafe|partial|opaque)\s', raw, re.M)
assert not re.search(r'(skipKernelTC|implemented_by|ofReduceBool)', raw)
assert len(re.findall(r'^theorem ', raw, re.M)) == 10
assert len(re.findall(r'^noncomputable def ', raw, re.M)) == 4
assert len(re.findall(r'^abbrev ', raw, re.M)) == 1
git('diff', '--check', BASE)
print(json.dumps(dict(status='PASS_SOURCE_PRESERVATION_ONLY', base=BASE,
    additive_files=len(expected), new_theorem_bodies=10, new_noncomputable_defs=4,
    new_abbreviations=1, source_derived_project_imports=81, including_target=82,
    checked_primary_sources=len(inventory['primary_sources']),
    accepted_gate_and_sources_unchanged=True, no_compiler_push_or_CI=True,
    mathematical_independent_review='pending', kernel_acceptance='not run'), indent=2))
