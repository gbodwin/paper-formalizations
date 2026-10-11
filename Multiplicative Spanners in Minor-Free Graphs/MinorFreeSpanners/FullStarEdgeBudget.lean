import MinorFreeSpanners.FullStarSurplusBudget

namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Actual host edges are retained up to the proved internal forest loss,
all directed collision charges and the actual ordered bad-pair score. -/
theorem IsStarPacking.fullContraction_edges_ge_budget {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (hfull : ∀ b ∈ C, (L b).card=ell) :
    G.edgeFinset.card ≤ (fullStarContraction G C L).edgeFinset.card+ell*C.card+
      4*(∑ b ∈ C, ∑ z : V, starCollision G L b z)+badStarPairCount G C L := by
  have hAC : Disjoint A C := (Finset.disjoint_coe.mp hG.disjoint).mono_right hCB
  let cost : Sym2 (StarContractionVertex C L) → ℕ :=
    Sym2.lift ⟨fullStarFiberLoss G C L,fullStarFiberLoss_symm G C L⟩
  have hsum := edge_cost_le_ordered_pairs (fullStarContraction G C L) cost
  have hordered : (∑ i : StarContractionVertex C L, ∑ j : StarContractionVertex C L,
      cost s(i,j)) ≤ 4*(∑ b ∈ C, ∑ z : V, starCollision G L b z)+badStarPairCount G C L := by
    simpa only [cost,Sym2.lift_mk] using h.full_ordered_fiber_loss_le hG hCB
  have hbound := hsum.trans hordered
  have hc (e : Sym2 (StarContractionVertex C L)) : cost e =
      (((quotientCrossEdges G (fullStarLabel C L)).filter fun a =>
        Sym2.map (fullStarLabel C L) a=e).card-1) := by
    induction e using Sym2.inductionOn with
    | hf i j => rfl
  simp_rw [hc] at hbound
  have he := h.fullContraction_edge_loss hAC hfull
  omega

/-- Actual mate-free common-neighbor counts replace every collision term
in the full covering contraction bound. -/
theorem IsStarPacking.fullContraction_edges_ge_mateFree_budget {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (q : ℝ) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G q (L b:Set V)) :
    (G.edgeFinset.card:ℝ) ≤ (fullStarContraction G C L).edgeFinset.card+
      ((ell:ℝ)+4*((ell*(ell-1):ℕ):ℝ)*q)*C.card+(badStarPairCount G C L:ℝ) := by
  have hc : ((∑ b ∈ C, ∑ z : V, starCollision G L b z : ℕ):ℝ) ≤
      ((ell*(ell-1):ℕ):ℝ)*q*C.card := by
    push_cast
    calc
      _ ≤ ∑ b ∈ C, ((ell*(ell-1):ℕ):ℝ)*q := by
        apply Finset.sum_le_sum
        intro b hb
        have hh := MateFreeOn.ordered_collision_budget G (L b) q (hfree b hb)
        rw [hfull b hb] at hh
        simpa only [starCollision,starCrossLeaves,Nat.cast_sum] using hh
      _ = _ := by simp [mul_comm]
  have he := Nat.cast_le (α:=ℝ).mpr (h.fullContraction_edges_ge_budget hG hCB hfull)
  push_cast at he hc ⊢
  nlinarith

end MinorFreeSpanners
