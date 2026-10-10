import LightEFTSpanners.ConnectivityOptimum

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- A positive-weight input edge forces a genuinely positive denominator in
any actual connectivity preserver, already under the empty fault set. -/
theorem preserver_weight_pos_of_adj {G Q : SimpleGraph V} {w : Sym2 V → ℝ} {q : ℕ}
    (hQ : IsFTConnectivityPreserver G Q q) (hw : ∀ e∈G.edgeSet,0<w e)
    {a b : V} (hab : G.Adj a b) : 0<totalWeight Q w := by
  classical
  have hr : Q.Reachable a b := by
    have h := (hQ.2 ∅ (by simp) a b).mp (by simpa [afterFaults] using hab.reachable)
    simpa [afterFaults] using h
  obtain ⟨p⟩ := hr
  cases p with
  | nil => exact False.elim (G.irrefl hab)
  | @cons u v z huv p =>
    unfold totalWeight
    apply sum_pos'
    · intro e he
      exact (hw e (edgeSet_mono hQ.1 (mem_edgeFinset.mp he))).le
    · exact ⟨s(a,v),mem_edgeFinset.mpr huv,hw _ ((mem_edgeSet G).mpr (hQ.1 huv))⟩

/-- Under the paper's positive actual-edge weights, zero preserver weight is
possible exactly for an edgeless input. No ratio convention creates nontrivial
zero-denominator examples. -/
theorem preserver_weight_zero_iff_input_bot {G Q : SimpleGraph V}
    {w : Sym2 V → ℝ} {q : ℕ} (hQ : IsFTConnectivityPreserver G Q q)
    (hw : ∀ e∈G.edgeSet,0<w e) : totalWeight Q w=0 ↔ G=⊥ := by
  constructor
  · intro hz
    apply le_antisymm _ bot_le
    intro a b hab
    have hp := preserver_weight_pos_of_adj hQ hw hab
    rw [hz] at hp
    exact False.elim (lt_irrefl 0 hp)
  · intro hG
    unfold totalWeight
    apply sum_eq_zero
    intro e he
    have hmem : e∈G.edgeSet := edgeSet_mono hQ.1 (mem_edgeFinset.mp he)
    rw [hG] at hmem
    simp only [edgeSet_bot, Set.mem_empty_iff_false] at hmem
end LightEFTSpanners
