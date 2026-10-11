import MinorFreeSpanners.GeneralLargeVertexBudget
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! If more than half the original vertices are small and residual, the
actual two local maximality bounds construct an unbalanced bipartite
subgraph. Its left degree retains the explicit (2+3k) error coefficient. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem residual_bipartite_of_large_residual (G : SimpleGraph V) (k ell : ℕ)
    (C : Finset V) (L : V → Finset V) (K eps1 d : ℝ)
    (hk : 8 ≤ k) (hell : 4*ell ≤ k) (hd : 0 < d) (hp : 0 < eps1*d)
    (hK : 4*(k:ℝ)^2 ≤ K)
    (hE : (G.edgeFinset.card:ℝ) ≤ d*(Fintype.card V:ℝ))
    (hF : IsGeneralStarForest G k C L)
    (hmin : ∀ x ∈ smallResidualVertices G C L (K*d), d ≤ (G.degree x:ℝ))
    (hres : ∀ x ∈ smallResidualVertices G C L (K*d),
      ((smallResidualNeighbors G C L (K*d) x).card:ℝ) ≤ 2*eps1*d)
    (hbranch : ∀ b ∈ C, (largeResidualStarVertices G C L (K*d) (3*eps1*d) b).card ≤ 1)
    (hlarge : Fintype.card V < 2*(smallResidualVertices G C L (K*d)).card) :
    ∃ X Y : Finset V, ∃ H : SimpleGraph V, H ≤ G ∧
      H.IsBipartiteWith (X:Set V) (Y:Set V) ∧ X.Nonempty ∧ ell*Y.card ≤ X.card ∧
      ∀ x ∈ X, d-(2+3*(k:ℝ))*eps1*d ≤ (H.degree x:ℝ) := by
  classical
  let U := smallResidualVertices G C L (K*d)
  let Y := residualTargetVertices G C L (K*d) (3*eps1*d)
  let W := weakResidualVertices G C L (K*d) (3*eps1*d) (d-(2+3*(k:ℝ))*eps1*d)
  let X := U \ W
  have hWU : W ⊆ U := fun _ hx => (Finset.mem_filter.mp hx).1
  have hW : k*W.card ≤ Fintype.card V :=
    (weakResidualVertices_card_bound G k C L (K*d) eps1 d hp hmin hres).trans
      (Finset.card_le_univ _)
  have hY : 2*k*Y.card ≤ 3*Fintype.card V :=
    residualTargetVertices_scaled_card G k C L K d (3*eps1*d) (by omega) hd hK hE hF hbranch
  have hW8 : 8*W.card ≤ Fintype.card V := (Nat.mul_le_mul_right W.card hk).trans hW
  have hY8 : 8*(ell*Y.card) ≤ 3*Fintype.card V := by
    have hh := Nat.mul_le_mul_right (2*Y.card) hell
    nlinarith
  have hcard : X.card+W.card=U.card := Finset.card_sdiff_add_card_eq_card hWU
  have hsize : ell*Y.card ≤ X.card := by
    change Fintype.card V < 2*U.card at hlarge
    omega
  have hX : X.Nonempty := by
    apply Finset.card_pos.mp
    change Fintype.card V < 2*U.card at hlarge
    omega
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxU := (Finset.mem_sdiff.mp hx).1
    have hxR := (Finset.mem_filter.mp hxU).1
    have hxD := (Finset.mem_filter.mp hxU).2
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (not_lt_of_ge hxD) (Finset.mem_filter.mp hy).2
    · exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_filter.mp hy).1
  let H := G.between (X:Set V) (Y:Set V)
  refine ⟨X,Y,H,SimpleGraph.between_le,SimpleGraph.between_isBipartiteWith
    (Finset.disjoint_coe.mpr hXY),hX,hsize,?_⟩
  intro x hx
  have hxY : x ∉ Y := fun hy => Finset.disjoint_left.mp hXY hx hy
  have hNF : H.neighborFinset x=Y.filter (G.Adj x) := by
    ext y
    simp [H,SimpleGraph.mem_neighborFinset,SimpleGraph.between_adj,hx,hxY,and_comm]
  have hdg : H.degree x=(Y.filter (G.Adj x)).card := congrArg Finset.card hNF
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdg ⊢
  rw [hdg]
  apply le_of_not_gt
  intro hh
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1,hh⟩)

end MinorFreeSpanners
