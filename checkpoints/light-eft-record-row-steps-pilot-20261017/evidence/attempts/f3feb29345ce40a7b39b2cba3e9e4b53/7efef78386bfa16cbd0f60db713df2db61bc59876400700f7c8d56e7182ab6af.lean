import LightEFTSpanners.EmpiricalAlgorithmGuarantees
import LightEFTSpanners.FaultBudgetSaturation

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] in
 theorem query_count_le (l : List (Sym2 V)) (eligible : Sym2 V → Finset J) :
    (l.map (fun e => (eligible e).card)).sum ≤ l.length*Fintype.card J := by
  induction l with
  | nil => simp
  | cons e es ih =>
    have hc := card_le_univ (eligible e)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

omit [Fintype J] in
 theorem input_length_le_square (G Q : SimpleGraph V) (w : Sym2 V → ℝ) :
    (input G Q w).length ≤ (Fintype.card V)^2 := by
  have h := card_le_univ (input G Q w).toFinset
  rw [List.toFinset_card_of_nodup (input_nodup G Q w)] at h
  have hs := Fintype.card_le_of_surjective Sym2.mk.uncurry (Sym2.mk_surjective (α:=V))
  have ht : Fintype.card (Sym2 V)≤(Fintype.card V)^2 := by
    simpa only [Fintype.card_prod,pow_two] using hs
  exact h.trans ht

omit [Fintype J] in
 theorem component_index_card_le (q : ℕ) (F : Fin (q+1) → SimpleGraph V) :
    Fintype.card (ForestComponentIndex F)≤(q+1)*Fintype.card V := by
  classical
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : Fin (q+1), Fintype.card V := by
      apply sum_le_sum
      intro i _
      exact Fintype.card_le_of_surjective (F i).connectedComponentMk Quot.mk_surjective
    _ = _ := by simp

omit [Fintype J] in
/-- Simple-graph saturation makes the input empty when q is large. Thus the
actual number of reached candidate/host queries is bounded by n^4 for every q. -/
theorem constructed_query_count_le (G Q : SimpleGraph V) (w : Sym2 V → ℝ)
    (q : ℕ) (hQ : IsFTConnectivityPreserver G Q q) (F : Fin (q+1) → SimpleGraph V) :
    ((input G Q w).map (fun e => (componentEligible univ F e).card)).sum ≤ (Fintype.card V)^4 := by
  classical
  by_cases hn : Fintype.card V≤q+2
  · have he := preserver_eq_at_large_budget hQ hn
    subst Q
    have hi : input G G w=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      have hh := (mem_input G G w e).mp he
      exact hh.2 hh.1
    simp [hi]
  · have hq : q+1≤Fintype.card V := by omega
    have h := query_count_le (input G Q w) (componentEligible univ F)
    have hi := input_length_le_square G Q w
    have hc := component_index_card_le q F
    have hc' : Fintype.card (ForestComponentIndex F)≤(Fintype.card V)^2 := by
      calc
        _ ≤ (q+1)*Fintype.card V := hc
        _ ≤ (Fintype.card V)*(Fintype.card V) := Nat.mul_le_mul_right _ hq
        _ = _ := (pow_two _).symm
    calc
      _ ≤ (input G Q w).length*Fintype.card (ForestComponentIndex F) := h
      _ ≤ (Fintype.card V)^2*(Fintype.card V)^2 := Nat.mul_le_mul hi hc'
      _ = _ := by ring
end LightEFTSpanners.SampledGreedy
