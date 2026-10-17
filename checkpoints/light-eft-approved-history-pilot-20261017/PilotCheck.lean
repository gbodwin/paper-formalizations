import LightEFTSpanners.VotingAdmissionHistory
open LightEFTSpanners.SampledGreedy
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.SampledGreedy.ApprovedHistory
  let some c := env.find? name | throwError "ApprovedHistory missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "ApprovedHistory not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: ApprovedHistory safe, total, computable, explicit List.rec, no partial companion"
namespace HistoryCases
open Finset LightEFTSpanners
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable
variable (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ) (f h : ℕ)
variable (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
variable (e g : Sym2 V) (A B : Finset J) (rs : List (Sym2 V × Finset J))
-- Arbitrary-state kernel propositions, not numerical probability evaluation.
example : ApprovedHistory Q w t f h eligible host [] := True.intro
example : ApprovedHistory Q w t f h eligible host [(e,A)] ↔
    A⊆eligible e ∧ h≤A.card ∧ ∀ j∈A,1/4≤testProbability Q Q (host j) w t f e := by
  simp only [ApprovedHistory_cons,ApprovedHistory_nil,List.map_nil,List.toFinset_nil,union_empty,true_and]
example : ApprovedHistory Q w t f h eligible host [(e,A),(g,B)] ↔
    (B⊆eligible g ∧ h≤B.card ∧ ∀ j∈B,1/4≤testProbability Q Q (host j) w t f g) ∧
    A⊆eligible e ∧ h≤A.card ∧ ∀ j∈A,1/4≤testProbability Q (Q∪{g}) (host j) w t f e := by
  simp only [ApprovedHistory_cons,ApprovedHistory_nil,List.map_cons,List.map_nil,
    List.toFinset_cons,List.toFinset_nil,insert_empty_eq,union_empty,true_and]
example (ht : ¬ ApprovedHistory Q w t f h eligible host rs) :
    ¬ ApprovedHistory Q w t f h eligible host ((e,A)::rs) := fun v => ht v.1
example (hs : ¬ A⊆eligible e) :
    ¬ ApprovedHistory Q w t f h eligible host ((e,A)::rs) := fun v => hs v.2.1
example (hc : ¬ h≤A.card) :
    ¬ ApprovedHistory Q w t f h eligible host ((e,A)::rs) := fun v => hc v.2.2.1
example (hp : ¬ ∀ j∈A,1/4≤testProbability Q (Q∪(rs.map Prod.fst).toFinset) (host j) w t f e) :
    ¬ ApprovedHistory Q w t f h eligible host ((e,A)::rs) := fun v => hp v.2.2.2
example (v : ApprovedHistory Q w t f h eligible host ((e,A)::rs)) :
    ApprovedHistory Q w t f h eligible host rs := v.1
example (v : ApprovedHistory Q w t f h eligible host ((e,A)::rs)) : A⊆eligible e := v.2.1
example (v : ApprovedHistory Q w t f h eligible host ((e,A)::rs)) : h≤A.card := v.2.2.1
example (v : ApprovedHistory Q w t f h eligible host ((e,A)::rs)) :
    ∀ j∈A,1/4≤testProbability Q (Q∪(rs.map Prod.fst).toFinset) (host j) w t f e := v.2.2.2
example (ht : ApprovedHistory Q w t f h eligible host rs) (hs : A⊆eligible e)
    (hc : h≤A.card)
    (hp : ∀ j∈A,testProbability Q (Q∪(rs.map Prod.fst).toFinset) (host j) w t f e = 1/4) :
    ApprovedHistory Q w t f h eligible host ((e,A)::rs) :=
  ⟨ht,hs,hc,fun j hj => (hp j hj).ge⟩
example (j : J) (hj : j∈A)
    (hp : testProbability Q (Q∪(rs.map Prod.fst).toFinset) (host j) w t f e < 1/4) :
    ¬ ApprovedHistory Q w t f h eligible host ((e,A)::rs) :=
  fun v => (not_le_of_gt hp) (v.2.2.2 j hj)
example : ApprovedHistory Q w t f 0 eligible host [(e,∅),(e,∅)] := by
  simp [ApprovedHistory_cons,ApprovedHistory_nil]
example (hh : 0<h) : ¬ ApprovedHistory Q w t f h eligible host [(e,∅)] := by
  intro v
  exact (Nat.not_le_of_gt hh) (by simpa using v.2.2.1)
example : ApprovedHistory (V:=Fin 0) (J:=Nat) ∅ (fun _ => -1) (-2) 999 999
    (fun _ => ∅) (fun _ => ∅) [] := True.intro
end HistoryCases
run_cmd Lean.logInfo "PASS: 16 kernel-checked history validation cases; four conjuncts, tail-derived accepted edges, exact inclusive quarter threshold, duplicate records, empty voters, empty vertices and arbitrary signed parameters"
