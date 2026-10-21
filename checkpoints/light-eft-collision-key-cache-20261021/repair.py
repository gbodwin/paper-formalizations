"""Exact finite source transform of c46; offline only, no compiler or runtime."""
from pathlib import Path
import hashlib,subprocess
H=Path(__file__).resolve().parent;R=H.parents[1]
BASE='c46b0a6b66a67b86d5de7a16f3bf38983571d2a5'
AUDIT='checkpoints/light-eft-joint-flag-assignment-local-repair-20261018/staged/JointAssignmentLawAudit.lean'
FIXTURE='checkpoints/light-eft-audit-text-cache-20261021/staged/SerializationEquivalenceFixtures.lean'
ENGINE='checkpoints/light-eft-joint-flag-ci-extension-revision-20261019/ci_text_fixture.py'
COMPOSITE='checkpoints/light-eft-audit-text-fixture-adapter-20261021/staged/ResolveAfterTextEquivalence.lean'
ORIGINAL='checkpoints/light-eft-joint-flag-assignment-corrected-draft-20261018/staged/ResolveJointAssignmentLawTarget.lean'
def base(path):return subprocess.check_output(['git','-C',str(R),'show',BASE+':'+path]).decode()
HELPER='''/- Per-module keys are seeded exclusively from the still-live environment,
before reading any new part. Raw-reader Names are lookup arguments only, never
inserted. Values are independently allocated bytes from the unchanged encoder.
This cache never enters State, so it cannot retain a newly read region. -/
abbrev KeyCache := Std.HashMap Name ByteArray

@[inline] def rememberKey (cache : KeyCache) (name : Name) : KeyCache :=
  if cache.contains name then cache
  else cache.insert name (ownedKey name)

@[inline] def keyFor (cache : KeyCache) (name : Name) : ByteArray :=
  match cache.get? name with
  | some key => key
  | none => ownedKey name

'''
SEED='''  let mut keys : KeyCache := {}
  if let some mod := data[owner]? then
    for info in mod.constants do
      keys := rememberKey keys info.name
'''
def audit_source():
    s=base(AUDIT)
    edits=[('private def hexKey',HELPER+'private def hexKey'),
      ('consumeNames (parts : OwnedParts) (owner : Nat)', 'consumeNames (parts : OwnedParts) (keys : KeyCache) (owner : Nat)'),
      ('(ownedKey name) false','(keyFor keys name) false'),
      ('(ownedKey name) true','(keyFor keys name) true'),
      ('consumeDeclarations (data : Array ModuleData) (owner : Nat)', 'consumeDeclarations (data : Array ModuleData) (keys : KeyCache) (owner : Nat)'),
      ('let freshKey := ownedKey info.name','let freshKey := keyFor keys info.name'),
      ('  let parts : OwnedParts :=',SEED+'  let parts : OwnedParts :='),
      ('consumeNames parts owner initial','consumeNames parts keys owner initial'),
      ('consumeDeclarations data owner state','consumeDeclarations data keys owner state')]
    for a,b in edits:
        assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
    return s
def fixture_source():
    audit=audit_source();start=audit.index('private partial def appendNat');end=audit.index('private def hexKey')
    helpers='namespace LightEFTAuditCollision\nopen Lean\n\n'+audit[start:end]+'end LightEFTAuditCollision\n\n'
    tests='''open Lean in
run_cmd do
  let base : Array Name := #[.anonymous, .str .anonymous "", .str .anonymous "alpha",
    .num .anonymous 0, .str .anonymous "0", .num (.str .anonymous "alpha") 123456789012345678901234567890,
    .str (.str .anonymous "odd name") "日本語", .str .anonymous "é", .str .anonymous "é",
    .str .anonymous "a\\tb\\nc", .str (.num (.str .anonymous "_private") 42) "helper",
    .str .anonymous "a.»", .str (.str .anonymous "a") "»"]
  let mut deep : Name := .anonymous
  for i in [:128] do deep := .num (.str deep "段") i
  let names := base.push deep
  for seeds in #[#[], names, names ++ names, #[names[0]!, names[2]!, names[3]!]] do
    let mut cache : LightEFTAuditCollision.KeyCache := {}
    for name in seeds do cache := LightEFTAuditCollision.rememberKey cache name
    let expected := seeds.foldl (fun (s : NameSet) n => s.insert n) {}
    unless cache.size == expected.size do throwError "Owned-key cache merged distinct Names"
    for name in names ++ names do
      let direct := LightEFTAuditCollision.ownedKey name
      unless LightEFTAuditCollision.keyFor cache name == direct do
        throwError "Owned-key cache differs from direct lossless encoding"
      if let some stored := cache.get? name then
        unless stored == direct do throwError "Owned-key cache invariant differs"
    unless (LightEFTAuditCollision.keyFor cache (.num .anonymous 0)) !=
        (LightEFTAuditCollision.keyFor cache (.str .anonymous "0")) do
      throwError "Owned-key cache confused numeric and string components"

'''
    s=base(FIXTURE);assert s.startswith('import Lean\n\n')
    return s.replace('import Lean\n\n','import Lean\n\n'+helpers+tests,1)
def expected():
    fixture=fixture_source();engine=base(ENGINE)
    old=hashlib.sha256(base(FIXTURE).encode()).hexdigest();new=hashlib.sha256(fixture.encode()).hexdigest()
    assert engine.count(old)==1;engine=engine.replace(old,new)
    header=b'/- Reviewed schedule: exact serialization fixture, then unchanged singleton resolver. -/\n'
    composite=(header+fixture.encode()+b'\n'+base(ORIGINAL).encode()[len(b'import Lean\n'):]).decode()
    return {AUDIT:audit_source(),FIXTURE:fixture,ENGINE:engine,COMPOSITE:composite}
if __name__=='__main__':
    for path,text in expected().items():(R/path).write_text(text)
