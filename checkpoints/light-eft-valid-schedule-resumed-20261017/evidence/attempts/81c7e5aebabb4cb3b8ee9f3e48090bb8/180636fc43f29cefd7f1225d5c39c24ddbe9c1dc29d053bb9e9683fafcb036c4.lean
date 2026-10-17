import LightEFTSpanners.StoredCandidateRefinement
open LightEFTSpanners.StoredCandidates
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredCandidates.ValidSchedule
  let some c := env.find? name | throwError "ValidSchedule missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "ValidSchedule not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: ValidSchedule safe, total, computable, explicit List.rec, no partial companion"
namespace ScheduleCases
open LightEFTSpanners
variable {n : ℕ} {J : Type*} [DecidableEq J]
variable (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
variable (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
variable (tape : SampledGreedy.Tape (Fin n) J) (h : ℕ) (R T : TypedInput n)
-- These are kernel-checked proposition cases, not a decidable runtime oracle.
example : ValidSchedule Q w t eligible host tape h [] E := True.intro
example : ValidSchedule Q w t eligible host tape h [R] E ↔
    R.budget=t*w s(R.edge.1,R.edge.2) ∧ HostRepresentation E eligible host tape R := by
  simp only [ValidSchedule_cons,ValidSchedule_nil,and_true]
example : ValidSchedule Q w t eligible host tape h [R,T] E ↔
    R.budget=t*w s(R.edge.1,R.edge.2) ∧ HostRepresentation E eligible host tape R ∧
    T.budget=t*w s(T.edge.1,T.edge.2) ∧ HostRepresentation (updated Q E w h R) eligible host tape T := by
  simp only [ValidSchedule_cons,ValidSchedule_nil,and_true]
example (rs : List (TypedInput n)) (hb : R.budget ≠ t*w s(R.edge.1,R.edge.2)) :
    ¬ ValidSchedule Q w t eligible host tape h (R::rs) E := fun v => hb v.1
example (rs : List (TypedInput n)) (hr : ¬ HostRepresentation E eligible host tape R) :
    ¬ ValidSchedule Q w t eligible host tape h (R::rs) E := fun v => hr v.2.1
example (rs : List (TypedInput n)) (ht : ¬ ValidSchedule Q w t eligible host tape h rs (updated Q E w h R)) :
    ¬ ValidSchedule Q w t eligible host tape h (R::rs) E := fun v => ht v.2.2
example (rs : List (TypedInput n)) (v : ValidSchedule Q w t eligible host tape h (R::rs) E) :
    R.budget=t*w s(R.edge.1,R.edge.2) := v.1
example (rs : List (TypedInput n)) (v : ValidSchedule Q w t eligible host tape h (R::rs) E) :
    HostRepresentation E eligible host tape R := v.2.1
example (rs : List (TypedInput n)) (v : ValidSchedule Q w t eligible host tape h (R::rs) E) :
    ValidSchedule Q w t eligible host tape h rs (updated Q E w h R) := v.2.2
example (ha : accept Q E w h R = true) :
    ValidSchedule Q w t eligible host tape h [R,T] E ↔
      R.budget=t*w s(R.edge.1,R.edge.2) ∧ HostRepresentation E eligible host tape R ∧
      T.budget=t*w s(T.edge.1,T.edge.2) ∧ HostRepresentation (R.edge::E) eligible host tape T := by
  simp only [ValidSchedule_cons,ValidSchedule_nil,and_true,updated,ha,ite_true]
example (ha : accept Q E w h R = false) :
    ValidSchedule Q w t eligible host tape h [R,T] E ↔
      R.budget=t*w s(R.edge.1,R.edge.2) ∧ HostRepresentation E eligible host tape R ∧
      T.budget=t*w s(T.edge.1,T.edge.2) ∧ HostRepresentation E eligible host tape T := by
  simp only [ValidSchedule_cons,ValidSchedule_nil,and_true,updated,ha,Bool.false_eq_true,ite_false]
example : ValidSchedule Q w t eligible host tape 0 [R,T] E ↔
    R.budget=t*w s(R.edge.1,R.edge.2) ∧ HostRepresentation E eligible host tape R ∧
    T.budget=t*w s(T.edge.1,T.edge.2) ∧ HostRepresentation (R.edge::E) eligible host tape T := by
  simp [ValidSchedule_cons,ValidSchedule_nil,updated,accept]
example : ValidSchedule Q w t eligible host tape 0 [R,R] E ↔
    R.budget=t*w s(R.edge.1,R.edge.2) ∧ HostRepresentation E eligible host tape R ∧
    R.budget=t*w s(R.edge.1,R.edge.2) ∧ HostRepresentation (R.edge::E) eligible host tape R := by
  simp [ValidSchedule_cons,ValidSchedule_nil,updated,accept]
example : ValidSchedule (n:=0) (J:=Nat) [] (fun _ => -1) (-2) (fun _ => ∅)
    (fun _ => ∅) (fun _ _ _ => []) 999 [] [] := True.intro
-- Concrete negative-scale/negative-budget and duplicate-state cases.
def concrete : TypedInput 1 := ⟨(0,0),-3/2,[]⟩
theorem concrete_rep (E : List (Fin 1 × Fin 1)) :
    HostRepresentation E (fun _ => (∅ : Finset Nat)) (fun _ => ∅) (fun _ _ _ => []) concrete := by
  exact ⟨[],(fun _ => ⟨[],[]⟩),by simp,rfl,rfl,by simp,by simp⟩
example : ValidSchedule [] (fun _ : Sym2 (Fin 1) => 3/4) (-2) (fun _ => (∅ : Finset Nat))
    (fun _ => ∅) (fun _ _ _ => []) 0 [concrete,concrete] [(0,0),(0,0)] := by
  rw [ValidSchedule_cons]
  refine ⟨by norm_num [concrete],concrete_rep _,?_⟩
  rw [ValidSchedule_cons]
  exact ⟨by norm_num [concrete],concrete_rep _,True.intro⟩
example : ¬ ValidSchedule [] (fun _ : Sym2 (Fin 1) => 3/4) 2 (fun _ => (∅ : Finset Nat))
    (fun _ => ∅) (fun _ _ _ => []) 0 [concrete] [] := by
  intro hbad
  have hb := hbad.1
  norm_num [concrete] at hb
end ScheduleCases
run_cmd Lean.logInfo "PASS: 16 kernel-checked schedule validation cases; exact budget/representation/tail conjuncts, accepted/rejected updated states, duplicate records, empty and zero-vertex cases, negative scale and mismatched budget"
