import LightEFTSpanners.EmpiricalVotingGreedy
open LightEFTSpanners.SampledGreedy
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.SampledGreedy.AccurateTrace
  let some c := env.find? name | throwError "AccurateTrace missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "AccurateTrace not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: AccurateTrace safe, total, computable, explicit List.rec, no partial companion"
namespace TraceCases
open Finset LightEFTSpanners
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable
variable (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f h : ℕ)
variable (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V)) (tape : Tape V J)
variable (e g : Sym2 V) (es : List (Sym2 V))
-- Kernel propositions: execution states and tape queries remain literal.
example : AccurateTrace Q w t f eligible host tape h [] := True.intro
example : AccurateTrace Q w t f eligible host tape h [e] ↔ ∀ j∈eligible e, |estimate Q (Q) (host j) w t e (tape (Q) e j)-testProbability Q (Q) (host j) w t f e|≤1/8 := by
  simp only [AccurateTrace_cons,AccurateTrace_nil,edges,true_and]
example : AccurateTrace Q w t f eligible host tape h [e,g] ↔
    (∀ j∈eligible g, |estimate Q (Q) (host j) w t g (tape (Q) g j)-testProbability Q (Q) (host j) w t f g|≤1/8) ∧ (∀ j∈eligible e, |estimate Q (edges Q w t eligible host tape h [g]) (host j) w t e (tape (edges Q w t eligible host tape h [g]) e j)-testProbability Q (edges Q w t eligible host tape h [g]) (host j) w t f e|≤1/8) := by
  rw [AccurateTrace_cons,AccurateTrace_cons,AccurateTrace_nil]
  simp only [edges,true_and]
example (ht : ¬ AccurateTrace Q w t f eligible host tape h es) :
    ¬ AccurateTrace Q w t f eligible host tape h (e::es) := fun v => ht v.1
example (hc : ¬ ∀ j∈eligible e, |estimate Q (edges Q w t eligible host tape h es) (host j) w t e (tape (edges Q w t eligible host tape h es) e j)-testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e|≤1/8) :
    ¬ AccurateTrace Q w t f eligible host tape h (e::es) := fun v => hc v.2
example (v : AccurateTrace Q w t f eligible host tape h (e::es)) : AccurateTrace Q w t f eligible host tape h es := v.1
example (v : AccurateTrace Q w t f eligible host tape h (e::es)) (j : J) (hj : j∈eligible e) :
    |estimate Q (edges Q w t eligible host tape h es) (host j) w t e (tape (edges Q w t eligible host tape h es) e j)-testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e|≤1/8 := v.2 j hj
example (j : J) (hj : j∈eligible e) (hb : 1/8<|estimate Q (edges Q w t eligible host tape h es) (host j) w t e (tape (edges Q w t eligible host tape h es) e j)-testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e|) :
    ¬ AccurateTrace Q w t f eligible host tape h (e::es) := fun v => (not_le_of_gt hb) (v.2 j hj)
example (ht : AccurateTrace Q w t f eligible host tape h es)
    (heq : ∀ j∈eligible e, |estimate Q (edges Q w t eligible host tape h es) (host j) w t e (tape (edges Q w t eligible host tape h es) e j)-testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e|=1/8) :
    AccurateTrace Q w t f eligible host tape h (e::es) := ⟨ht,fun j hj => (heq j hj).le⟩
example (ht : AccurateTrace Q w t f eligible host tape h es)
    (heq : ∀ j∈eligible e, estimate Q (edges Q w t eligible host tape h es) (host j) w t e (tape (edges Q w t eligible host tape h es) e j)-testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e = 1/8) :
    AccurateTrace Q w t f eligible host tape h (e::es) := by
  refine ⟨ht,?_⟩
  intro j hj
  rw [heq j hj]
  norm_num
example (ht : AccurateTrace Q w t f eligible host tape h es)
    (heq : ∀ j∈eligible e, estimate Q (edges Q w t eligible host tape h es) (host j) w t e (tape (edges Q w t eligible host tape h es) e j)-testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e = -(1/8)) :
    AccurateTrace Q w t f eligible host tape h (e::es) := by
  refine ⟨ht,?_⟩
  intro j hj
  rw [heq j hj]
  norm_num
example (ht : AccurateTrace Q w t f eligible host tape h es)
    (heq : ∀ j∈eligible e, estimate Q (edges Q w t eligible host tape h es) (host j) w t e (tape (edges Q w t eligible host tape h es) e j)-testProbability Q (edges Q w t eligible host tape h es) (host j) w t f e = 0) :
    AccurateTrace Q w t f eligible host tape h (e::es) := by
  refine ⟨ht,?_⟩
  intro j hj
  rw [heq j hj]
  norm_num
example : AccurateTrace Q w t f (fun _ => (∅ : Finset J)) host tape h es := by
  induction es with
  | nil => exact True.intro
  | cons e es ih => exact ⟨ih,fun _ hj => False.elim (Finset.notMem_empty _ hj)⟩
example : AccurateTrace (V:=Fin 0) (J:=Nat) ∅ (fun _ => -1) (-2) 999
    (fun _ => ∅) (fun _ => ∅) (fun _ _ _ => []) 0 [] := True.intro
example (ha : h≤(votes Q w t eligible host tape Q g).card) : AccurateTrace Q w t f eligible host tape h [e,g] ↔
    AccurateTrace Q w t f eligible host tape h [g] ∧ (∀ j∈eligible e, |estimate Q (insert g Q) (host j) w t e (tape (insert g Q) e j)-testProbability Q (insert g Q) (host j) w t f e|≤1/8) := by
  rw [AccurateTrace_cons]
  have hstate : edges Q w t eligible host tape h [g] = insert g Q := by
    simp only [edges,ha,ite_true]
  rw [hstate]
example (ha : ¬ h≤(votes Q w t eligible host tape Q g).card) : AccurateTrace Q w t f eligible host tape h [e,g] ↔
    AccurateTrace Q w t f eligible host tape h [g] ∧ (∀ j∈eligible e, |estimate Q (Q) (host j) w t e (tape (Q) e j)-testProbability Q (Q) (host j) w t f e|≤1/8) := by
  rw [AccurateTrace_cons]
  have hstate : edges Q w t eligible host tape h [g] = Q := by
    simp only [edges,ha,ite_false]
  rw [hstate]
example : AccurateTrace Q w t f eligible host tape h [e,e] ↔
    AccurateTrace Q w t f eligible host tape h [e] ∧ (∀ j∈eligible e, |estimate Q (edges Q w t eligible host tape h [e]) (host j) w t e (tape (edges Q w t eligible host tape h [e]) e j)-testProbability Q (edges Q w t eligible host tape h [e]) (host j) w t f e|≤1/8) := Iff.rfl
end TraceCases
run_cmd Lean.logInfo "PASS: 17 kernel-checked trace validation cases; exact tail-derived execution and tape state, inclusive absolute-error eighth threshold and both signed boundaries, accepted/rejected branches, duplicate edges, empty eligibility and empty vertices"
