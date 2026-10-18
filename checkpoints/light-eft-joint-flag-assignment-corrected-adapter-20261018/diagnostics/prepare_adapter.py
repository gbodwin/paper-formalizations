"""Mechanical corrected-draft/released-receipt rebind; no runtime activation."""
from pathlib import Path
import ast, hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
OLD = ROOT / 'checkpoints/light-eft-joint-flag-assignment-adapter-20261018'
BASE = '41f4e793e8d56f754c152964b5af9c2445f2706e'
DRAFT = '7a4ab29cebfdd86808d4d6708411967fdb4a3bd4'
FAILED = 'a76e0478e7618284d1a978c4bba0672f885afcdf'
OLD_DRAFT = '33e162e467cea919ee60d2c17e1f13d8586caba3'

def write(name, data): (HERE/name).write_text(json.dumps(data, indent=2)+'\n')
def git_bytes(p):
    b = subprocess.check_output(['git','show',BASE+':'+str(p.relative_to(ROOT))],cwd=ROOT)
    assert p.read_bytes() == b
    return b
def once(s, old, new):
    assert s.count(old) == 1, old
    return s.replace(old,new,1)

files = sorted(OLD.glob('*.py')) + [OLD/n for n in ['inventory-policy.json','signature-supplement-summary.json','signature-supplement.jsonl']]
assert len(files)==20
for p in files: (HERE/p.name).write_bytes(git_bytes(p))

p=HERE/'probability_plan.py';s=p.read_text()
s=s.replace('joint-flag-assignment-draft-20261018','joint-flag-assignment-corrected-draft-20261018')
s=s.replace(OLD_DRAFT,DRAFT).replace('draft 33e162e4','corrected draft 7a4ab29c')
s=once(s,"require(len(rows)==26 and len({r['path'] for r in rows})==26", "require(len(rows)==22 and len({r['path'] for r in rows})==22")
anchor="require(commit not in {DRAFT_COMMIT,OLD_SOURCE_COMMIT,"
s=once(s,anchor,"require(commit not in {'"+OLD_DRAFT+"','"+BASE+"','b4503c44d81a60564d2318c4a9e982a448757818','"+FAILED+"',DRAFT_COMMIT,OLD_SOURCE_COMMIT,")
p.write_text(s)
p=HERE/'scope.py';s=once(p.read_text(),"APPROVED='"+OLD_DRAFT+"'","APPROVED='"+DRAFT+"'");p.write_text(s)
p=HERE/'test_adapter.py';s=p.read_text()
s=s.replace('f9446665c62e4e5c90b1578b930dd6ec','9dd0d7e576bc4fb7b7fa05d4413d4bff').replace('26141424860045dba7f6e2438abcf5615cef11b29b27b242ec24de5a9dc6e504','06054c674a4566e9b344b7fd4c4c12f646c1c2a7a6b74b315538ef4d34e21aa1')
s=once(s,"self.assertEqual(known['receipt']['commit'],'49f17551c0c092c9631f36e2108114cc83c8eebe')","self.assertEqual(known['receipt']['commit'],'"+FAILED+"')")
s=once(s,'for commit in [pp.SOURCE_SLOT,pp.ADAPTER_SLOT,',"for commit in ['"+OLD_DRAFT+"','"+BASE+"','b4503c44d81a60564d2318c4a9e982a448757818','"+FAILED+"',pp.SOURCE_SLOT,pp.ADAPTER_SLOT,")
anchor=' def test_stale_authority_stops_before_claim_work_evidence_or_lock(self):'
extra=''' def test_corrected_rebind_preserves_scope_and_fresh_paths(self):
  previous=pp.ROOT/'checkpoints/light-eft-joint-flag-assignment-draft-20261018'
  for name in ['project-dependency-bindings.json','project-dependency-bindings.jsonl','accepted-preservation-bindings.json','mathlib-interface-bindings.json']:
   self.assertEqual((pp.DRAFT_DIR/name).read_bytes(),(previous/name).read_bytes())
  self.assertEqual(scope.APPROVED,pp.DRAFT_COMMIT)
  self.assertEqual(pp.DRAFT_COMMIT,'DRAFT_COMMIT_VALUE')
  self.assertFalse(Path(RAW['future_work_root']).exists())
  self.assertFalse(Path(RAW['future_evidence_root']).exists())
  self.assertFalse((HERE/'production-invocation-claimed.json').exists())
  self.assertEqual(len(pp.REQUIRED_ROOTS),16);self.assertEqual(len(pp.REQUIRED_INTERFACES),8)
  for stage in RAW['commands']:
   self.assertEqual(stage['visible_admission_bytes'],(4 if stage['stage'] in ['replay','audit'] else 3)*1024**3)
   if stage['stage']!='replay':self.assertIn('-DwarningAsError=true',stage['argv'])
'''.replace('DRAFT_COMMIT_VALUE',DRAFT)
s=once(s,anchor,extra+anchor);p.write_text(s)

policy=json.loads((OLD/'accepted-preservation-policy.json').read_text());policy['reviewed_draft_commit']=DRAFT
write('accepted-preservation-policy.json',policy)
release=json.loads((OLD/'released-lock.json').read_text())
release['released_epoch']='9dd0d7e576bc4fb7b7fa05d4413d4bff'
release['receipt'].update(commit=FAILED,path='checkpoints/light-eft-joint-flag-assignment-draft-20261018/future-validation-evidence/lease.json',bytes=719,sha256='06054c674a4566e9b344b7fd4c4c12f646c1c2a7a6b74b315538ef4d34e21aa1')
write('released-lock.json',release)

rows=[];unchanged=[];changed=[]
for old in files:
    b=git_bytes(old);new=(HERE/old.name).read_bytes()
    rows.append(dict(path=old.name,base_path=str(old.relative_to(ROOT)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
    (unchanged if new==b else changed).append(old.name)
assert changed==['probability_plan.py','scope.py','test_adapter.py']
members={
 'driver.py':['execute_production','make_production_plan','_run_batch','run_fixture'],
 'scope.py':['reviewed_base_inputs','legacy_dependency_contract','reviewed_wrapper','Context','verify_receipts','reviewed_inputs','dependency_contract'],
 'semantic_inventory.py':['Inventory','load_prior','family','metadata_form','capture_signatures','add_immutable_accepted_object','exact_commands'],
 'focused_audit.py':['validate','table','chunk','verify_chunks','export_all'],
 'probability_plan.py':['source_binding','normalize_plan','translate_commands','preservation_contract','merge_preserved_inputs','reviewed_adapter_data'],
}
same=[]
for name,names in members.items():
    old={x.name:x for x in ast.parse((OLD/name).read_text()).body if isinstance(x,(ast.FunctionDef,ast.ClassDef))}
    new={x.name:x for x in ast.parse((HERE/name).read_text()).body if isinstance(x,(ast.FunctionDef,ast.ClassDef))}
    for member in names:
        assert ast.dump(old[member],include_attributes=False)==ast.dump(new[member],include_attributes=False),name+':'+member
        same.append(name+':'+member)
write('base-bindings.json',dict(implementation_commit=BASE,accepted_failed_evidence_commit=FAILED,files=rows))
write('scope-reconciliation.json',dict(base_implementation=BASE,base_files=len(files),changed=changed,unchanged=unchanged,
    ast_identical=same,allowed_changes='New draft/path/manifest-count and release bindings; old-authority rejection literals and synthetic tests only',
    reviewed_core_AST_members_unchanged=len(same),production_claim_absent=not (HERE/'production-invocation-claimed.json').exists(),
    Lean_invocations=0,common_lock_opened=False,lock_acquisitions=0))
print(json.dumps(dict(base=BASE,draft=DRAFT,changed=changed,unchanged=len(unchanged),identical_core_members=len(same),Lean_invocations=0,lock_acquisitions=0),indent=2))
