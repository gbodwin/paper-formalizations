"""Offline plan/proposal generator. Writes only this planning directory."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = 'cc147275808c734c93154bd397ca7e0d018dc5dd'
TARGET = 'LightEFTPaidJointBridgeStage.SuppliedResponseJointBridge'
PAID = 'checkpoints/light-eft-paid-focused-adapter-20261020'
DECODER = 'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'
ENGINE = 'checkpoints/light-eft-canonical-output-adapter-20261020'
FUTURE = 'checkpoints/light-eft-paid-joint-bridge-ci-adapter-20261020'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def dump(d):
    return (json.dumps(d, indent=2) + '\n').encode()

def write(rel, data):
    path = HERE / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as f:
        f.write(data.encode() if isinstance(data, str) else data)

def row(path, **extra):
    raw = (ROOT / path).read_bytes()
    assert raw == subprocess.check_output(['git', '-C', str(ROOT), 'show', BASE + ':' + path])
    return dict(path=path, bytes=len(raw), sha256=sha(raw), **extra)

paid = json.loads((ROOT / PAID / 'ci-spec.json').read_text())
decoder = json.loads((ROOT / DECODER / 'ci-spec.json').read_text())
catalog = {}
for r in paid['dependencies'] + decoder['dependencies']:
    assert r['module'] not in catalog or catalog[r['module']] == r['path']
    catalog[r['module']] = r['path']
staged = {}
for role, module in [('serialization', 'LightEFTPaidSamplingStage.PaidFlagSerialization'),
                     ('composition', 'LightEFTPaidSamplingStage.PaidFlagSampleComposition')]:
    catalog[module] = next(r['path'] for r in paid['sources'] if r['role'] == role)
    staged[module] = 'paid'
catalog[decoder['target']] = decoder['sources']['source']['path']
staged[decoder['target']] = 'decoder'
catalog[TARGET] = 'checkpoints/light-eft-paid-joint-bridge-20261020/staged/LightEFTPaidJointBridgeStage/SuppliedResponseJointBridge.lean'
seen, boundary = {}, set()

def visit(module):
    if module in seen:
        return
    record = row(catalog[module], module=module)
    imports = []
    for line in (ROOT / catalog[module]).read_text().splitlines():
        if line.startswith('import '):
            imports += line[7:].split('--', 1)[0].split()
    record['direct_imports'] = imports
    seen[module] = record
    for m in imports:
        if m in catalog:
            visit(m)
        else:
            assert not m.startswith(('LightEFT', 'LightSpanners')), m
            boundary.add(m)

visit(TARGET)
imports = sorted(set(seen) - {TARGET})
assert len(imports) == 80 and len(boundary) == 27
origins = [dict(seen[m], origin=staged.get(m, 'ordinary_build')) for m in imports]
assert sum(r['origin'] == 'ordinary_build' for r in origins) == 77
source = (ROOT / catalog[TARGET]).read_text()
roots = ['LightEFTSpanners.PaidJointBridge.' + n for n in re.findall(r'^theorem (\w+)', source, re.M)]
assert len(roots) == 12
interfaces = [
    'LightEFTSpanners.PaidFlagSerialization.execute_eq',
    'LightEFTSpanners.PaidFlagSampleComposition.full_trace',
    'LightEFTSpanners.PaidFlagSampleComposition.execute_eq',
    'LightEFTSpanners.StoredFlagSample.execute_encoded',
    'LightEFTSpanners.StoredFlagSample.typed_edgeSet',
    'LightEFTSpanners.JointFlagSampling.decoded_assignment_probability',
]
audit_base = (ROOT / PAID / 'staged/CompositionAudit.lean').read_text()
audit = audit_base.replace('import LightEFTPaidSamplingStage.PaidFlagSampleComposition\n', 'import ' + TARGET + '\n', 1)
audit = audit.replace('let target := "LightEFTPaidSamplingStage.PaidFlagSampleComposition".toName', 'let target := "' + TARGET + '".toName', 1)
name_array = lambda names: '#[' + ', '.join('"' + n + '".toName' for n in names) + ']'
audit = re.sub(r'  let requiredRoots : Array Name := #[^\n]+', '  let requiredRoots : Array Name := ' + name_array(roots), audit, count=1)
audit = re.sub(r'  let required : Array Name := #[^\n]+', '  let required : Array Name := ' + name_array(interfaces), audit, count=1)
block = lambda s: s.split('namespace LightEFTAuditCollision\n', 1)[1].split('end LightEFTAuditCollision', 1)[0]
assert block(audit) == block(audit_base)
write('proposed/staged/BridgeAudit.lean', audit)
resolver_base = (ROOT / PAID / 'staged/ResolveFocusedTarget.lean').read_text()
old_allowed = '[`LightEFTPaidSamplingStage.PaidFlagSerialization, `LightEFTPaidSamplingStage.PaidFlagSampleComposition]'
assert resolver_base.count(old_allowed) == 1
write('proposed/staged/ResolveBridgeTarget.lean', resolver_base.replace(old_allowed, '[`' + TARGET + ']'))

workflow_path = '.github/workflows/lean.yml'
before = (ROOT / workflow_path).read_text()
insertion = '''      - name: Verify supplied response output against joint decoder
        id: light_eft_paid_joint_bridge
        env:
          PYTHONPYCACHEPREFIX: ${{ runner.temp }}/light-eft-paid-joint-bridge-python-${{ github.run_id }}-${{ github.run_attempt }}
        run: python3 -B checkpoints/light-eft-paid-joint-bridge-ci-adapter-20261020/ci_gate.py
      - name: Preserve focused bridge evidence before remaining checks
        if: ${{ always() && steps.light_eft_paid_joint_bridge.outcome != 'skipped' }}
        uses: actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02
        with:
          name: light-eft-paid-joint-bridge-${{ github.run_id }}-${{ github.run_attempt }}
          path: ${{ runner.temp }}/light-eft-paid-joint-bridge-${{ github.run_id }}-${{ github.run_attempt }}
          include-hidden-files: true
          if-no-files-found: error
          retention-days: 30
'''
anchor = '      - name: Verify canonical actual-output corollary after three context replays\n'
assert before.count(anchor) == 1
after = before.replace(anchor, insertion + anchor, 1)
extra_path = '            ${{ runner.temp }}/light-eft-paid-joint-bridge-${{ github.run_id }}-${{ github.run_attempt }}\n'
old_path = '            ${{ runner.temp }}/light-eft-paid-focused-${{ github.run_id }}-${{ github.run_attempt }}\n'
assert after.count(old_path) == 1
after = after.replace(old_path, old_path + extra_path)
assert after.replace(insertion, '', 1).replace(extra_path, '', 1) == before
write('PROPOSED-WORKFLOW.yml', after)
proposed = {workflow_path: after.encode()}
changes = []
for path in [PAID + '/ci-spec.json', DECODER + '/ci-spec.json', ENGINE + '/ci-spec.json']:
    original = (ROOT / path).read_bytes()
    data = json.loads(original)
    modified = []
    for i, old in enumerate(data['engine_files']):
        if old['path'] in proposed:
            raw = proposed[old['path']]
            new = dict(path=old['path'], bytes=len(raw), sha256=sha(raw))
            data['engine_files'][i] = new
            modified.append(dict(before=old, after=new))
    expected = {workflow_path} | ({DECODER + '/ci-spec.json'} if path.startswith(ENGINE + '/') else set())
    assert {x['before']['path'] for x in modified} == expected
    proposed[path] = dump(data)
    changes.append(dict(path=path, before_sha256=sha(original), proposed_bytes=len(proposed[path]),
                        proposed_sha256=sha(proposed[path]), changed_bindings=modified))
write('SPEC-BINDING-UPDATES.json', dump(changes))
patch = ''
for path, raw in proposed.items():
    original = (ROOT / path).read_text()
    patch += 'diff --git a/' + path + ' b/' + path + '\n'
    patch += ''.join(difflib.unified_diff(original.splitlines(True), raw.decode().splitlines(True),
                                        fromfile='a/' + path, tofile='b/' + path))
write('REQUIRED-PRODUCTION-DELTA.patch', patch)

templates = [PAID + '/' + n for n in ['ci_gate.py', 'focused_context.py', 'output_guards.py', 'audit_check.py',
              'staged/CompositionAudit.lean', 'staged/ResolveFocusedTarget.lean']]
templates += [ENGINE + '/' + n for n in ['ci_handoff.py', 'ci_receipts.py', 'ci_admission_receipts.py',
              'child_runner.py', 'contracts.py', 'ci_accounting.py', 'ci_lease.py', 'ci_inventory.py',
              'package_selection.py', 'collision_coverage.py']]
templates += ['scripts/LightEFTCgroup.py', 'scripts/LightEFTProcessLifecycle.py']
prefixes = __import__('ast').literal_eval((ROOT / PAID / 'finite_contract.py').read_text().split('CONTRACT=', 1)[1])['project_prefixes']
plan = dict(
    kind='SOURCE_ONLY_PLAN_AND_PROPOSALS; NOT_IMPLEMENTED_OR_RUNNABLE', execution_enabled=False,
    reviewed_source_commit=BASE, accepted_runner_reference=dict(commit='2beb9958f70b975baeb58c9f46caaa24dfe79795', run_id=39471963506,
        run_attempt=1, qualification='Historical successful runner observations only; future full accounting/admission still mandatory'),
    target=TARGET, target_source=seen[TARGET], unchanged_reviewed_proof=True,
    project_imports=80, project_modules_with_target=81, dependencies=origins,
    external_boundary_imports=sorted(boundary), external_boundary_count=27,
    external_boundary_sources=[dict(module=m, package=('aesop' if m == 'Aesop' else 'mathlib'),
        source='.lake/packages/' + ('aesop' if m == 'Aesop' else 'mathlib') + '/' + m.replace('.', '/') + '.lean',
        object='.lake/packages/' + ('aesop' if m == 'Aesop' else 'mathlib') + '/.lake/build/lib/lean/' + m.replace('.', '/') + '.olean',
        package_commit=paid['pins']['aesop' if m == 'Aesop' else 'mathlib'],
        object_binding='fresh actual identity/bytes/hash plus all emitted semantic companions; no current bytes guessed in this plan')
        for m in sorted(boundary)],
    complete_external_input_policy='Normal ordinary-CI build/cache roots for all locked packages plus pinned toolchain; exhaustive CIInventory semantic membership and companion/runtime hashes; audit every actually loaded module against exact unique selected primary and bound companions; boundary list is not transitive manifest',
    toolchain=paid['toolchain'], tool_hashes=paid['tool_hashes'], pins=paid['pins'],
    source_and_object_integrity='Every source/helper/engine/spec/workflow byte equal exact event Git HEAD. Exact Git pins and tracked-clean package sources. Every selected object and emitted companion identity/bytes/hash sealed; all prior evidence and journals retained. No authenticated clean-cache or historical object provenance claim.',
    template_bindings=[row(p) for p in templates],
    staged_input_policy='HANDOFF-CONTRACT.md; original current-run physical output roots, full producer receipt/index validation, no previous-run downloads or transport manifest admission',
    root_order=['new bridge work/objects', 'same-run paid work/objects', 'same-run decoder work/objects', 'repository .lake/build/lib/lean', 'locked package .lake/build/lib/lean roots', 'pinned toolchain lib/lean'],
    stages=['compile', 'official exact singleton resolution', 'ordinary singleton kernel replay', 'full actual-owner declaration and recursive axiom audit'],
    stage_argv=dict(compile=['bin/lean', '-j1', '-s65536', '-M5120', '-DautoImplicit=false', '-DwarningAsError=true', '--root=reviewed bridge staged root', '-o', 'fresh exact target .olean', 'exact reviewed source'],
        resolve=['bin/lean', '-j1', '-s65536', '-M5120', '-DautoImplicit=false', '-DwarningAsError=true', 'bound ResolveBridgeTarget.lean'],
        replay=['bin/leanchecker', '-v', TARGET], audit=['bin/lean', '-j1', '-s65536', '-M5120', '-DautoImplicit=false', '-DwarningAsError=true', 'bound BridgeAudit.lean']),
    resources=dict(admission_GiB=dict(compile=3, resolve=3, replay=4, audit=4), cpu_seconds=dict(compile=60, resolve=60, replay=60, audit=90),
        wall_seconds=90, prespawn_seconds=300, address_space_bytes=12884901888, heap_MiB=5120, stack_KiB=65536, workers=1,
        stop_headroom_bytes=1073741824, RSS_stop_bytes=6442450944, anonymous_growth_stop_bytes=3221225472,
        core_bytes=0, ordinary_FSIZE_bytes=16777216, audit_file_bytes=67108864, audit_total_bytes=335544320,
        job_timeout_minutes=120, policy='unchanged full initial cgroup accounting, host/disk/PID/OOM, inherited lease FD, owned waitid/wait4/descendants and ECHILD release'),
    audit=dict(required_theorem_roots=roots, mathematical_definition_count=5, actual_owner_count='discover; never guess',
        all_actual_owner_private_generated_roots=True, recursive_types_and_bodies=True, inductive_constructor_recursor_links=True,
        required_reachable_interfaces=interfaces, allowed_axioms=['Classical.choice', 'Quot.sound', 'propext'],
        reject_project_axioms_unsafe_partial=True, exact_project_import_set=imports,
        project_prefixes=prefixes + ['LightEFTPaidJointBridgeStage'], collision_reader_unchanged=True),
    workflow=dict(insertion='after successful paid and decoder gates, before corollary gate; all existing checks preserved',
        immediate_evidence_upload=True, existing_final_upload_extended=True, no_new_job_or_dispatch=True,
        production_diff='REQUIRED-PRODUCTION-DELTA.patch', active_workflow_changed=False,
        prerequisite='finite adapter and modeled negative regressions in IMPLEMENTATION-CONTRACT.md implemented and independently reviewed first',
        timeout_qualification='Accepted run was about102 minutes; added work may exceed unchanged120-minute whole-job limit. A timeout remains failure; do not skip later gates.'),
    evidence='Complete failed/successful receipts, actual sources/objects/identities, raw logs, decisions, journals, resolutions, exhaustive audit tables, row-aligned chunks, collision read/free reports, full evidence index; result false until all four receipt verifications and clean release pass',
    stop_policy='First failure only; no automatic rerun/extra accepted dependency compile; preserve failed preflight and all CI evidence; any necessary proof fix must be separately bound and reviewed before publication',
    independent_review='Plan and source proposal pending; no compiler/push/CI authorization inferred from this document',
    remaining_math_scope='Charged enumeration/input construction, concrete response generator and flattened tape law, literal bank/caller handoff and aggregate costs remain open')
write('PLAN.json', dump(plan))
print(json.dumps(dict(imports=80, ordinary_sources=77, staged_sources=3, external_boundary=27,
                     proposed_workflow_sha256=sha(after.encode()), production_delta_sha256=sha(patch.encode())), indent=2))
