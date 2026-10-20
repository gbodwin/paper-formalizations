"""Static proposal consistency checks only. Never imports a runtime gate."""
from pathlib import Path
import ast
import collections
import difflib
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = 'cc147275808c734c93154bd397ca7e0d018dc5dd'
PAID = 'checkpoints/light-eft-paid-focused-adapter-20261020'
DECODER = 'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'
ENGINE = 'checkpoints/light-eft-canonical-output-adapter-20261020'
plan = json.loads((HERE / 'PLAN.json').read_text())
sha = lambda b: hashlib.sha256(b).hexdigest()
assert plan['execution_enabled'] is False
assert plan['kind'] == 'SOURCE_ONLY_PLAN_AND_PROPOSALS; NOT_IMPLEMENTED_OR_RUNNABLE'
assert plan['reviewed_source_commit'] == BASE
assert plan['project_imports'] == 80 and plan['project_modules_with_target'] == 81
assert len(plan['dependencies']) == len({r['module'] for r in plan['dependencies']}) == 80
assert collections.Counter(r['origin'] for r in plan['dependencies']) == {'ordinary_build': 77, 'paid': 2, 'decoder': 1}
for r in [plan['target_source'], *plan['dependencies'], *plan['template_bindings']]:
    b = (ROOT / r['path']).read_bytes()
    assert b == subprocess.check_output(['git', '-C', str(ROOT), 'show', BASE + ':' + r['path']])
    assert len(b) == r['bytes'] and sha(b) == r['sha256']
assert plan['target_source']['sha256'] == 'b3ba8f73669c5eea04e58cdb545866382771b6e12537a32cd437d8f13d5b7664'
assert len(plan['external_boundary_sources']) == plan['external_boundary_count'] == 27
assert {r['module'] for r in plan['external_boundary_sources']} == set(plan['external_boundary_imports'])
for r in plan['external_boundary_sources']:
    assert r['package_commit'] == plan['pins'][r['package']]
    assert r['object'].endswith(r['module'].replace('.', '/') + '.olean')
    assert r['source'].endswith(r['module'].replace('.', '/') + '.lean')
assert len(plan['audit']['required_theorem_roots']) == 12
assert set(plan['audit']['exact_project_import_set']) == {r['module'] for r in plan['dependencies']}
assert plan['resources']['admission_GiB'] == {'compile': 3, 'resolve': 3, 'replay': 4, 'audit': 4}
assert plan['resources']['job_timeout_minutes'] == 120

audit = (HERE / 'proposed/staged/BridgeAudit.lean').read_text()
old_audit = (ROOT / PAID / 'staged/CompositionAudit.lean').read_text()
collision = lambda s: s.split('namespace LightEFTAuditCollision\n', 1)[1].split('end LightEFTAuditCollision', 1)[0]
assert collision(audit) == collision(old_audit)
mask = lambda s: re.sub(r'  let required(?:Roots)? : Array Name := #[^\n]+', '<finite name array>',
                       s.replace('import ' + plan['target'] + '\n', 'import LightEFTPaidSamplingStage.PaidFlagSampleComposition\n')
                        .replace('"' + plan['target'] + '".toName', '"LightEFTPaidSamplingStage.PaidFlagSampleComposition".toName'))
assert mask(audit) == mask(old_audit)
resolver = (HERE / 'proposed/staged/ResolveBridgeTarget.lean').read_text()
old_resolver = (ROOT / PAID / 'staged/ResolveFocusedTarget.lean').read_text()
assert resolver == old_resolver.replace('[`LightEFTPaidSamplingStage.PaidFlagSerialization, `LightEFTPaidSamplingStage.PaidFlagSampleComposition]', '[`' + plan['target'] + ']')

workflow_path = '.github/workflows/lean.yml'
before = (ROOT / workflow_path).read_text()
after = (HERE / 'PROPOSED-WORKFLOW.yml').read_text()
start = after.index('      - name: Verify supplied response output against joint decoder\n')
end = after.index('      - name: Verify canonical actual-output corollary after three context replays\n')
extra_path = '            ${{ runner.temp }}/light-eft-paid-joint-bridge-${{ github.run_id }}-${{ github.run_attempt }}\n'
assert (after[:start] + after[end:]).replace(extra_path, '', 1) == before
assert after.index('id: light_eft_staged') < start < end
proposed = {workflow_path: after.encode()}
updates = json.loads((HERE / 'SPEC-BINDING-UPDATES.json').read_text())
assert [x['path'] for x in updates] == [PAID + '/ci-spec.json', DECODER + '/ci-spec.json', ENGINE + '/ci-spec.json']
patch = ''
for record in updates:
    path = record['path']
    original = (ROOT / path).read_bytes()
    assert sha(original) == record['before_sha256']
    data = json.loads(original)
    expected = {workflow_path} | ({DECODER + '/ci-spec.json'} if path.startswith(ENGINE + '/') else set())
    assert {r['before']['path'] for r in record['changed_bindings']} == expected
    for change in record['changed_bindings']:
        old, new = change['before'], change['after']
        assert old in data['engine_files'] and old['path'] == new['path']
        raw = proposed[new['path']]
        assert new == dict(path=old['path'], bytes=len(raw), sha256=sha(raw))
        data['engine_files'][data['engine_files'].index(old)] = new
    raw = (json.dumps(data, indent=2) + '\n').encode()
    assert len(raw) == record['proposed_bytes'] and sha(raw) == record['proposed_sha256']
    proposed[path] = raw
for path, raw in proposed.items():
    patch += 'diff --git a/' + path + ' b/' + path + '\n'
    patch += ''.join(difflib.unified_diff((ROOT / path).read_text().splitlines(True), raw.decode().splitlines(True), fromfile='a/' + path, tofile='b/' + path))
assert patch == (HERE / 'REQUIRED-PRODUCTION-DELTA.patch').read_text()
subprocess.check_call(['git', '-C', str(ROOT), 'apply', '--check', str(HERE / 'REQUIRED-PRODUCTION-DELTA.patch')])
for p in HERE.glob('*.py'):
    ast.parse(p.read_text())
changes = subprocess.check_output(['git', '-C', str(ROOT), 'diff', '--name-only', BASE]).decode().splitlines()
assert all(p.startswith(HERE.relative_to(ROOT).as_posix() + '/') for p in changes)
print(json.dumps(dict(status='PASS_STATIC_PLAN_ONLY', exact_project_imports=80, ordinary_sources=77,
    same_run_staged_sources=3, explicit_external_source_origins=27, audit_project_modules=81,
    reviewed_bridge_source_unchanged=True, collision_and_recursive_reader_unchanged=True,
    live_workflow_or_existing_specs_modified=False, proposed_spec_updates=3,
    production_delta_sha256=sha(patch.encode()), implementation_complete=False,
    compiler_or_CI_or_push_launched=False), indent=2))
