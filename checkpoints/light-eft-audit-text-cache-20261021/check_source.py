"""Finite offline delta/binding checks; no runtime gate, compiler or admission."""
from pathlib import Path
import ast,copy,hashlib,json,subprocess
H=Path(__file__).resolve().parent;R=H.parents[1]
BASE='515a39d143901c75b2c457f674f6b28d766b51d3'
AUDIT='checkpoints/light-eft-joint-flag-assignment-local-repair-20261018/staged/JointAssignmentLawAudit.lean'
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
sha=lambda b:hashlib.sha256(b).hexdigest()
old=git('show',BASE+':'+AUDIT).decode();new=(R/AUDIT).read_text()
start=new.index('/- Serialization-only memoization.');end=new.index('end LightEFTAuditText')+len('end LightEFTAuditText')
helper=new[start:end]
assert old.split('end LightEFTAuditCollision')[0]==new.split('end LightEFTAuditCollision')[0]
assert 'abbrev Cache := Std.HashMap Name String' in helper
assert helper.count('toString name')==1 and 'cache.get? name' in helper and 'cache.insert name text' in helper
assert 'unsafe' not in helper and 'partial' not in helper and 'IO.' not in helper
restored=new[:start]+new[end+2:]
restored=restored.replace('  let mut textCache : LightEFTAuditText.Cache := {}\n','')
restored=restored.replace('''    let (ownerText, afterOwner) := LightEFTAuditText.renderName textCache (owner n)
    let (nameText, afterName) := LightEFTAuditText.renderName afterOwner n
    textCache := afterName
    inventory := inventory ++ s!"{ownerText}\\t{nameText}\\t{kind c}\\t{c.isUnsafe}\\t{c.isPartial}\\n"''','''    inventory := inventory ++ s!"{owner n}\\t{n}\\t{kind c}\\t{c.isUnsafe}\\t{c.isPartial}\\n"''')
restored=restored.replace('''    let (nameText, afterName) := LightEFTAuditText.renderName textCache n
    let (ownerText, afterOwner) := LightEFTAuditText.renderName afterName (owner n)
    let (typeText, afterType) := LightEFTAuditText.renderNames afterOwner typeDeps
    let (bodyText, afterBody) := LightEFTAuditText.renderNames afterType bodyDeps
    textCache := afterBody
    dependencies := dependencies ++ s!"{nameText}\\t{ownerText}\\t{kind c}\\t{typeText}\\t{bodyText}\\t{c.isUnsafe}\\t{c.isPartial}\\n"''','''    let fmt := fun (ns : Array Name) => String.intercalate "," (ns.toList.map toString)
    dependencies := dependencies ++ s!"{n}\\t{owner n}\\t{kind c}\\t{fmt typeDeps}\\t{fmt bodyDeps}\\t{c.isUnsafe}\\t{c.isPartial}\\n"''')
assert restored==old,'Delta exceeds exact pure TSV name rendering replacement'
fixture=(H/'staged/SerializationEquivalenceFixtures.lean').read_text()
assert fixture[fixture.index('/- Serialization-only memoization.'):fixture.index('end LightEFTAuditText')+len('end LightEFTAuditText')]==helper
assert fixture.startswith('import Lean\n') and 'import LightEFT' not in fixture
assert 'String.intercalate "," (names.toList.map toString)' in fixture
specnames=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
 'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020','light-eft-fair-bit-batch-ci-adapter-20261021']
bound=0;changes=[]
def row(path):
 raw=(R/path).read_bytes();return dict(path=path,bytes=len(raw),sha256=sha(raw))
for n in specnames:
 p='checkpoints/'+n+'/ci-spec.json';a=json.loads(git('show',BASE+':'+p));b=json.loads((R/p).read_text());expected=copy.deepcopy(a)
 if n=='light-eft-joint-flag-ci-extension-revision-20261019':expected['sources']['audit']=row(AUDIT)
 for i,r in enumerate(expected['engine_files']):expected['engine_files'][i]=row(r['path'])
 assert b==expected,'Unexpected semantic or engine-path changes: '+p
 assert len(b['engine_files'])==len(a['engine_files']) and [r['path'] for r in b['engine_files']]==[r['path'] for r in a['engine_files']]
 for r in b['engine_files']:assert r==row(r['path']);bound+=1
 for before,after in zip(a['engine_files'],b['engine_files'],strict=True):
  if before!=after:changes.append(dict(spec=p,path=after['path']))
 if n=='light-eft-joint-flag-ci-extension-revision-20261019':assert b['sources']['source']==a['sources']['source'] and b['sources']['resolver']==a['sources']['resolver']
allowed={AUDIT,*['checkpoints/'+n+'/ci-spec.json' for n in specnames]}
paths=git('diff','--name-only',BASE).decode().splitlines()+git('ls-files','--others','--exclude-standard').decode().splitlines()
assert all(p in allowed or p.startswith(str(H.relative_to(R))+'/') for p in paths)
for p in H.glob('*.py'):ast.parse(p.read_text())
source_bindings=H/'SOURCE-BINDINGS.json'
if source_bindings.exists():
 manifest=json.loads(source_bindings.read_text())
 assert manifest['baseline']==BASE and manifest['actual_Lean_runtime_gain']=='unmeasured'
 for r in manifest['bindings']:assert r==row(r['path']),'Source review binding drift: '+r['path']
git('diff','--check',BASE)
print(json.dumps(dict(status='PASS_EXACT_SOURCE_BINDINGS_ONLY',baseline=BASE,
 collision_region_code_byte_identical=True,reverse_serialization_replacement_restores_entire_audit=True,
 traversal_checks_exports_order_headers_final_PASS_unchanged=True,paper_theorem_and_resolver_unchanged=True,
 workflow_runtime_resource_limits_unchanged=True,other_audit_clones_unchanged=True,
 engine_binding_rows_checked=bound,changed_engine_rows=changes,
 native_Lean_fixture='unelaborated; exact helper body copy',compiler_push_CI=False,
 actual_Lean_performance='unmeasured; no timeout-fit claim',independent_review='pending'),indent=2))
