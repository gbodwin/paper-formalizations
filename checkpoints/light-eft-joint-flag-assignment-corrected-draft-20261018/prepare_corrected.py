"""Prepare an uncompiled correction; local Git/source reads and new draft writes only."""
from pathlib import Path
import copy, hashlib, json, os, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OLD = ROOT / 'checkpoints/light-eft-joint-flag-assignment-draft-20261018'
OLD_COMMIT = '33e162e467cea919ee60d2c17e1f13d8586caba3'
FAILED = 'a76e0478e7618284d1a978c4bba0672f885afcdf'
WORK = ROOT / '.lake/joint-flag-assignment-corrected-24dc9cb766304db7a30ef80a8abe0dbd'
EVIDENCE = HERE / 'future-validation-evidence'
MODULE = 'LightEFTJointFlagSamplingStage.JointAssignmentLaw'

def guard(event, args):
    if event == 'subprocess.Popen':
        assert args[0] == 'git' and args[1][:2] == ['git', 'show']
    if event in ['fcntl.flock', 'os.fork', 'os.posix_spawn']:
        raise AssertionError('No compiler, locking or activation')
    if event == 'open' and isinstance(args[0], (str, bytes, os.PathLike)):
        p = os.path.abspath(os.fsdecode(args[0]))
        assert p != '/tmp/distance-sparsification-single-compiler.lock'
        assert not p.startswith(('/proc/', '/sys/'))
sys.addaudithook(guard)

def sha(b): return hashlib.sha256(b).hexdigest()
def load(p): return json.loads(p.read_text())
def write(name, obj): (HERE / name).write_text(json.dumps(obj, indent=2) + '\n')
def bind(p):
    p = Path(p)
    assert p.is_absolute() and p.is_file() and not p.is_symlink()
    st = p.stat(); b = p.read_bytes()
    return dict(path=str(p), bytes=len(b), sha256=sha(b),
                identity=[st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns])
def authenticated(p, commit):
    b = subprocess.check_output(['git', 'show', commit + ':' + str(p.relative_to(ROOT))], cwd=ROOT)
    assert b == p.read_bytes()
    return b
def replace_once(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new, 1)

assert not WORK.exists() and not EVIDENCE.exists()
manifest = load(OLD / 'manifest.json')
authenticated(OLD / 'manifest.json', OLD_COMMIT)
for row in manifest['entries']:
    p = OLD / row['path']; b = authenticated(p, OLD_COMMIT)
    assert len(b) == row['bytes'] and sha(b) == row['sha256']

source_rel = Path('staged/LightEFTJointFlagSamplingStage/JointAssignmentLaw.lean')
original = (OLD / source_rel).read_text()
source = replace_once(original,
    '  change (∑ x : I → α, (∏ i, p.mass (x i)) *\n'
    '      (if y = (fun i => g (x i)) then 1 else 0)) =\n'
    '    ∏ i, ∑ a, p.mass a * (if y i = g a then 1 else 0)',
    '  dsimp only [Law.map, Law.bind, Law.pure, productLaw]')
source = replace_once(source,
    'if P (Fin.cons b bs) then ∏ i, p.mass ((Fin.cons b bs) i) else 0',
    'if P (Fin.cons b bs) then\n'
    '        ∏ i : Fin (k+1), p.mass ((Fin.cons (α := fun _ : Fin (k+1) => α) b bs) i) else 0')
source = replace_once(source, 'variable {J : Type*} [Fintype J] [DecidableEq J]',
    'variable {J : Type*} [fintypeJ : Fintype J] [decidableEqJ : DecidableEq J]')
source = replace_once(source,
    '  exact ((List.nodup_finRange _).reverse).product\n'
    '    ((Finset.nodup_toList _).product ((List.nodup_finRange _).product (Finset.nodup_toList _)))',
    '  exact List.Nodup.product (List.nodup_reverse.mpr (List.nodup_finRange _))\n'
    '    (List.Nodup.product (Finset.nodup_toList _)\n'
    '      (List.Nodup.product (List.nodup_finRange _) (Finset.nodup_toList _)))')
source = replace_once(source,
    '  simp only [samplingSchedule, List.length_product, List.length_reverse,\n'
    '    List.length_finRange, Finset.length_toList, Finset.card_univ, Nat.mul_assoc]',
    '  unfold samplingSchedule\n'
    '  change (((List.finRange l.length).reverse ×ˢ\n'
    '      ((univ : Finset J).toList ×ˢ\n'
    '        (List.finRange m ×ˢ (univ : Finset (OriginalEdge n)).toList))).length) =\n'
    '    l.length * Fintype.card J * m * Fintype.card (OriginalEdge n)\n'
    '  simp only [List.length_product, List.length_reverse, List.length_finRange,\n'
    '    Finset.length_toList, Finset.card_univ, Nat.mul_assoc]')
for name in ['samplingSchedule_nodup', 'mem_samplingSchedule', 'samplingSchedule_length']:
    source = replace_once(source, 'theorem ' + name + ' ', 'include decidableEqJ in\ntheorem ' + name + ' ')
for name in ['decodeHost_typed', 'decodeAssignment_head', 'decodeAssignment_outside']:
    source = replace_once(source, 'theorem ' + name + ' ', 'include fintypeJ decidableEqJ in\ntheorem ' + name + ' ')
assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial)\b', source)
headers = lambda s: dict(re.findall(r'^theorem (\w+)(.*?)(?= :=|\n  \|)', s, re.M | re.S))
assert len(headers(original)) == 16 and headers(original) == headers(source)

# Every mathematical definition and abbreviation is kept verbatim. The only
# changes are the four local proof repairs, names of existing instances and includes.
def definitions(text):
    result = {}
    for match in re.finditer(r'^(?:noncomputable )?(?:def|abbrev) (\w+)', text, re.M):
        tail = text[match.start():]
        end = re.search(r'\n\n', tail)
        result[match[1]] = tail[:end.start()] if end else tail
    return result
assert definitions(original) == definitions(source)
(HERE / source_rel).parent.mkdir(parents=True)
(HERE / source_rel).write_text(source)
for rel in ['staged/JointAssignmentLawAudit.lean', 'staged/ResolveJointAssignmentLawTarget.lean']:
    (HERE / rel).write_bytes((OLD / rel).read_bytes())

copies = ['accepted-preservation-bindings.json', 'project-dependency-bindings.json',
          'project-dependency-bindings.jsonl', 'mathlib-interface-bindings.json',
          'interface-bindings.json', 'interface-declarations.txt']
for rel in copies: (HERE / rel).write_bytes((OLD / rel).read_bytes())
closure = load(HERE / 'project-dependency-bindings.json')
assert len(closure['dependencies']) == 77
for row in closure['dependencies']:
    for role in ['source', 'object']: assert bind(row[role]['path']) == row[role]
for row in load(HERE / 'accepted-preservation-bindings.json')['objects']:
    for role in ['source', 'object']: assert bind(row[role]['path']) == row[role]
for row in load(HERE / 'mathlib-interface-bindings.json')['interfaces']:
    for role in ['source', 'object']: assert bind(row[role]['path']) == row[role]
export = HERE / 'project-closure-export'; export.mkdir()
old_export = load(OLD / 'project-closure-export/manifest.json')
for part in old_export['parts']:
    (export / part['path']).write_bytes((OLD / 'project-closure-export' / part['path']).read_bytes())
old_export['source'] = str(HERE / 'project-dependency-bindings.jsonl')
(export / 'manifest.json').write_text(json.dumps(old_export, indent=2) + '\n')
assert b''.join((export / p['path']).read_bytes() for p in old_export['parts']) == (HERE / 'project-dependency-bindings.jsonl').read_bytes()

plan = load(OLD / 'focused-validation-plan.json')
old_work = plan['future_work_root']
def relocate(value):
    if isinstance(value, str): return value.replace(str(OLD), str(HERE)).replace(old_work, str(WORK))
    if isinstance(value, list): return [relocate(x) for x in value]
    if isinstance(value, dict): return {k: relocate(v) for k, v in value.items()}
    return value
plan = relocate(plan)
bindings = {key: bind(HERE / rel) for key, rel in [
    ('source', source_rel), ('audit', 'staged/JointAssignmentLawAudit.lean'),
    ('resolver', 'staged/ResolveJointAssignmentLawTarget.lean')]}
plan.update(bindings)
for key, rel in [('accepted_staged_preservation', 'accepted-preservation-bindings.json'),
                 ('project_closure', 'project-dependency-bindings.json'),
                 ('mathlib_interface_bindings', 'mathlib-interface-bindings.json')]: plan[key] = bind(HERE / rel)
roles = [['source'], ['resolver', 'source'], ['source'], ['audit', 'source']]
for command, keys in zip(plan['commands'], roles):
    command['submitted_sources'] = [bindings[k] for k in keys]
    command['launcher_config_bytes_with_placeholders'] = len(json.dumps(dict(argv=command['argv'], env=command['environment'], stage=command['stage'])).encode())
    assert command['launcher_config_bytes_with_placeholders'] <= 4096
    assert command['executed'] is False
release_path = OLD / 'future-validation-evidence/lease.json'
release_bytes = authenticated(release_path, FAILED)
assert len(release_bytes) == 719 and sha(release_bytes) == '06054c674a4566e9b344b7fd4c4c12f646c1c2a7a6b74b315538ef4d34e21aa1'
release = json.loads(release_bytes)
assert release['epoch'] == '9dd0d7e576bc4fb7b7fa05d4413d4bff' and release['state'] == 'released' and release['kernel_echild']
plan['known_last_accepted_release'] = dict(receipt=bind(release_path), accepted_evidence_commit=FAILED,
    epoch=release['epoch'], device=33, inode=3258, directory_identity=[33,1],
    qualification='Accepted failed-attempt receipt only; no common-lock open or acquisition in preparation.')
plan['status'] = 'CORRECTED UNCOMPILED SOURCE/PLAN DRAFT; no execution authority'
plan['interface_review'] += ' Corrections address the accepted failed attempt only; no elaboration or acceptance claimed.'
assert plan['resource_profile'] == load(OLD / 'focused-validation-plan.json')['resource_profile']
write('focused-validation-plan.json', plan)
(HERE / 'planned-commands.txt').write_text('UNEXECUTED; exact new draft/adapter commits require independent review.\n' + '\n'.join(json.dumps(x, indent=2) for x in plan['commands']) + '\n')
write('draft-bindings.json', dict(module=MODULE, theorem=plan['theorem'], **bindings,
    compiled_object=None, kernel_replay=None, Lean_audit=None, Lean_invocations=0))
layout = relocate(load(OLD / 'package-layout-prediction.json'))
write('package-layout-prediction.json', layout)

mathlib = Path('/workspace/paper-formalizations/.lake/packages/mathlib')
references = [
    (ROOT / 'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean', 27, 43),
    (ROOT / 'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteProductLaw.lean', 1, 15),
    (mathlib / 'Mathlib/Data/Fin/Tuple/Basic.lean', 110, 119),
    (mathlib / 'Mathlib/Data/Fin/Tuple/Basic.lean', 182, 192),
    (mathlib / 'Mathlib/Data/List/Nodup.lean', 230, 235),
    (mathlib / 'Mathlib/Data/List/Nodup.lean', 308, 316),
    (mathlib / 'Mathlib/Data/List/ProdSigma.lean', 45, 55),
]
write('pinned-source-references.json', [dict(binding=bind(p), first_line=a, last_line=b,
    excerpt='\n'.join(p.read_text().splitlines()[a-1:b])) for p,a,b in references])
write('static-reconciliation.json', dict(kind='Source-text and immutable binding checks only, no elaboration',
    predecessor_draft=OLD_COMMIT, accepted_failed_evidence=FAILED,
    source=bindings['source'], all_16_source_theorem_headers_identical=True,
    definitions_and_abbreviations_identical=sorted(definitions(original)),
    existing_instance_types_unchanged=['Fintype J','DecidableEq J'],
    include_decidableEqJ=['samplingSchedule_nodup','mem_samplingSchedule','samplingSchedule_length'],
    include_fintypeJ_decidableEqJ=['decodeHost_typed','decodeAssignment_head','decodeAssignment_outside'],
    dependency_binding_bytes_identical=True, dependency_count=77, imported_project_count=78,
    required_roots=16, required_interfaces=8, accepted_pairs_unchanged=3,
    future_paths_absent=True, Lean_invocations=0, common_lock_opened=False, lock_acquisitions=0))
write('preservation.json', dict(prior_failed_evidence=FAILED,
    accepted_objects=load(HERE / 'accepted-preservation-bindings.json')['objects'],
    latest_release_receipt=bind(release_path), Lean_invocations=0, common_lock_opened=False,
    lock_acquisitions=0, real_inventory_scans=0, retrieval=False))
print(json.dumps(dict(source=bindings['source'], unchanged_headers=16,
    unchanged_definitions=sorted(definitions(original)), dependencies=77,
    future_work=str(WORK), future_evidence=str(EVIDENCE), Lean_invocations=0, lock_acquisitions=0), indent=2))
