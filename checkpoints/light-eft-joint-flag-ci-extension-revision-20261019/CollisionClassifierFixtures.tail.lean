/- Source-only fixture tail. The Python regression generator prepends the exact
production helper (with import Lean only). No fixture has been executed here.
Synthetic ConstantInfo records test metadata compatibility, not kernel proofs.
A future run requires a separate reviewed bounded supervisor/ownership plan. -/
namespace LightEFTClassifierGenerated

def equationSource : Nat → Nat
  | 0 => 0
  | n+1 => n

open Lean Lean.Elab.Command in
run_cmd do
  liftTermElabM do
    let some equations ← Lean.Meta.getEqnsFor? ``equationSource |
      throwError "Native fixture failed to generate equation theorems"
    unless !equations.isEmpty do throwError "No generated equation theorem"
    for name in equations do
      let env := (← getEnv).setExporting false
      let some (.thmInfo original) := env.find? name |
        throwError "Generated equation was not an actual theorem"
      let changed := { original with value := mkLet `copy original.type original.value (mkBVar 0) }
      unless LightEFTAuditCollision.subsumesInfo (fun n => env.find? n) (.thmInfo original) (.thmInfo changed) do
        throwError "Generated equation compatible-proof case rejected"
      let incompatible := { changed with levelParams := [`fixtureLevel] ++ changed.levelParams }
      if LightEFTAuditCollision.subsumesInfo (fun n => env.find? n) (.thmInfo original) (.thmInfo incompatible) then
        throwError "Generated equation incompatible-level case accepted"
    let some congr ← Lean.Meta.mkCongrSimp? (mkConst ``equationSource) |
      throwError "Native fixture failed to generate congruence theorem"
    let env := (← getEnv).setExporting false
    let name := Name.str ``equationSource "generatedCongr"
    let original : TheoremVal := { name, levelParams := [], type := congr.type, value := congr.proof }
    let changed := { original with value := mkLet `copy original.type original.value (mkBVar 0) }
    unless LightEFTAuditCollision.subsumesInfo (fun n => env.find? n) (.thmInfo original) (.thmInfo changed) do
      throwError "Generated congruence compatible-proof case rejected"
    let incompatible := { changed with all := [name, `other] }
    if LightEFTAuditCollision.subsumesInfo (fun n => env.find? n) (.thmInfo original) (.thmInfo incompatible) then
      throwError "Generated congruence incompatible-group case accepted"
  liftIO <| LightEFTAuditCollision.marker "CLASSIFIER-NATIVE: actual equation/congruence generators passed"

end LightEFTClassifierGenerated

namespace LightEFTAuditCollision
open Lean

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def theoremInfo (name : Name) (type value : Expr)
    (levels : List Name := []) (all : List Name := [name]) : ConstantInfo :=
  .thmInfo { name, levelParams := levels, type, value, all }

private def axiomInfo (name : Name) (type : Expr) (unsafeFlag := false) : ConstantInfo :=
  .axiomInfo { name, levelParams := [], type, isUnsafe := unsafeFlag }

private def definitionInfo (name : Name) (type value : Expr) : ConstantInfo :=
  .defnInfo { name, levelParams := [], type, value, hints := .opaque, safety := .safe }

private def moduleInfo (constants : Array ConstantInfo) (extras : Array Name := #[]) : ModuleData :=
  { (default : ModuleData) with constants, constNames := constants.map (·.name), extraConstNames := extras }

private def foldDeclarations (data : Array ModuleData) : IO State := do
  let mut state : State := {}
  for owner in [:data.size] do
    state ← consumeDeclarations data owner state
  return state

private def saveParts (file : System.FilePath) (main : ModuleData) (count : Nat := 3) : IO Unit :=
  saveModuleDataParts `CollisionClassifierFixture
    ((#[(file,{ main with isModule := true }),
        (OLeanLevel.server.adjustFileName file,{ (default : ModuleData) with isModule := true }),
        (OLeanLevel.private.adjustFileName file,{ main with isModule := true })]).extract 0 count)

unsafe def classifierFixtureMain (args : List String) : IO Unit := do
  let some directory := args.head? | throw <| IO.userError "Fresh fixture output path required"
  let root : System.FilePath := directory
  if ← root.pathExists then throw <| IO.userError "Fixture output already exists"
  IO.FS.createDirAll root
  let propType := mkConst `True
  let proofA := mkConst `True.intro
  let proofB := mkLet `h propType proofA (mkBVar 0)
  let predicate := axiomInfo `True (mkSort .zero)
  let lookup := fun name => if name == `True then some predicate else none
  for name in [Name.str `Generated "eq_1", Name.str `Generated "congr_1", Name.num `Arbitrary 129] do
    let a := theoremInfo name propType proofA
    let b := theoremInfo name propType proofB
    let ax := axiomInfo name propType
    ensure (subsumesInfo lookup a b && subsumesInfo lookup b a) "compatible theorem proofs"
    ensure (subsumesInfo lookup a ax && !subsumesInfo lookup ax a) "directed theorem/axiom rule"
    ensure (subsumesInfo lookup ax ax) "cheap proposition axiom rule"
    ensure (!subsumesInfo lookup a (axiomInfo name propType true)) "unsafe theorem/axiom mismatch"
    ensure (!subsumesInfo lookup a (theoremInfo name (mkConst `False) proofB)) "unequal types"
    ensure (!subsumesInfo lookup a (theoremInfo name propType proofB [] [name,`Other])) "mutual block mismatch"
    ensure (!subsumesInfo lookup a (theoremInfo name propType proofB [`u])) "level parameter mismatch"
    ensure (!subsumesInfo lookup (definitionInfo name propType proofA) (definitionInfo name propType proofA))
      "duplicate definition must remain incompatible"
  marker "CLASSIFIER-NATIVE: generated-equation/congruence compatibility and rejection passed"

  let alphaA := mkForall `a .default (mkConst `Nat) propType
  let alphaB := mkForall `b .implicit (mkConst `Nat) propType
  ensure (subsumesInfo lookup (theoremInfo `alpha alphaA proofA) (theoremInfo `alpha alphaB proofB))
    "Expr BEq must use alpha equivalence and ignore binder annotations"
  ensure (!subsumesInfo lookup (axiomInfo `nonprop (mkSort .zero)) (axiomInfo `nonprop (mkSort .zero)))
    "axiom types are not normalized or assumed propositions"
  ensure (!subsumesInfo (fun _ => none) (axiomInfo `missing propType) (axiomInfo `missing propType))
    "cheap proposition requires existing head declaration"
  ensure (subsumesInfo lookup (axiomInfo `unsafe propType true) (axiomInfo `unsafe propType true))
    "pinned axiom rule permits equal unsafe flags; separate recursive safety audit remains required"
  let predicateType := mkForall `x .default (mkConst `Nat) (mkSort .zero)
  let pred := axiomInfo `Predicate predicateType
  let lookupPred := fun n => if n == `Predicate then some pred else none
  let applied := mkApp (mkConst `Predicate) (mkConst `Nat.zero)
  ensure (isPropCheap lookupPred applied && !isPropCheap lookupPred (mkConst `Predicate))
    "exact predicate arity"

  let thm := theoremInfo `same propType proofA
  let ax := axiomInfo `same propType
  let forward ← foldDeclarations #[moduleInfo #[predicate],moduleInfo #[ax],moduleInfo #[thm]]
  let backward ← foldDeclarations #[moduleInfo #[predicate],moduleInfo #[thm],moduleInfo #[ax]]
  ensure (forward.compatible == 1 && backward.compatible == 1 &&
    (forward.declarations.get? (ownedKey `same)).map (·.owner) == some 2 &&
    (backward.declarations.get? (ownedKey `same)).map (·.owner) == some 1)
    "ordered finalizeImport update/retain"
  let early ← foldDeclarations #[moduleInfo #[ax],moduleInfo #[ax],moduleInfo #[predicate]]
  ensure (early.incompatible == 1) "future declarations cannot satisfy cheap proposition lookup"
  let malformedBase := moduleInfo #[thm]
  let malformed := { malformedBase with constNames := #[`different] }
  let malformedState ← foldDeclarations #[malformed]
  ensure (malformedState.unclassified == 1) "mismatched constNames/constants must reject"
  marker "CLASSIFIER-NATIVE: pinned predicate and ordered import fold passed"

  let fileA := root / "a.olean"
  let fileB := root / "b.olean"
  let complex := Name.num (Name.str .anonymous "α.β") (2^200+17)
  let a := theoremInfo complex propType proofA
  let b := theoremInfo complex propType proofB
  let data := #[moduleInfo #[a] #[complex],moduleInfo #[b] #[complex]]
  saveParts fileA data[0]!
  saveParts fileB data[1]!
  let first ← scanOne data 0 fileA {}
  let second ← scanOne data 1 fileB first
  ensure (second.compatible == 1 && second.incompatible == 0 && second.unclassified == 0 &&
    second.parts == 6 && second.freed == 6 && second.peakRegions == 3 &&
    (second.declarations.get? (ownedKey complex)).map (·.owner) == some 1)
    "owned typed locations and keys survive independently freed/reloaded regions"
  let extraOnly := #[moduleInfo #[] #[`aux],moduleInfo #[] #[`aux]]
  let extrasFile := root / "extras.olean"
  saveParts extrasFile extraOnly[0]!
  let e1 ← scanOne extraOnly 0 extrasFile {}
  let e2 ← scanOne extraOnly 1 extrasFile e1
  ensure (e2.auxiliaryOverlaps > 0 && e2.actualDeclarations == 0 && e2.incompatible == 0)
    "auxiliary ownership must not become a declaration collision"
  for count in [1,2] do
    let missing := root / s!"missing-{count}.olean"
    saveParts missing data[0]! count
    let mut rejected := false
    try
      let _ ← scanOne data 0 missing {}
      pure ()
    catch _ => rejected := true
    ensure rejected "missing required part accepted"
  marker "CLASSIFIER-NATIVE: owned region cleanup and missing-part rejection passed"
  marker "CLASSIFIER-NATIVE-FIXTURES: passed"

end LightEFTAuditCollision

unsafe def main (args : List String) : IO Unit :=
  LightEFTAuditCollision.classifierFixtureMain args
