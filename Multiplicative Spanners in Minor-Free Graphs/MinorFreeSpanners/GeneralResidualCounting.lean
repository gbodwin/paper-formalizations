import MinorFreeSpanners.MaximumForestBranchBound
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Literal original-host residual and crossing counts. The exceptional
covered vertices are selected by their actual residual neighborhood size.
The low-vertex crossing budget pays for every low vertex, not merely the
number of exceptional vertices. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def smallResidualVertices (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D : ℝ) : Finset V :=
  (starResidual C L).filter (fun x => (G.degree x:ℝ) ≤ D)

noncomputable def exceptionalCoveredVertices (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D threshold : ℝ) : Finset V :=
  (C.biUnion (fun b => insert b (L b))).filter
    (fun x => threshold ≤ (smallResidualNeighbors G C L D x).card)

noncomputable def graphCrossingCount (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  ∑ x ∈ A, (B.filter (G.Adj x)).card

theorem smallResidualNeighbors_eq_filter (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D : ℝ) (x : V) :
    smallResidualNeighbors G C L D x = (smallResidualVertices G C L D).filter (G.Adj x) := by
  ext y
  simp only [smallResidualNeighbors,smallResidualVertices,Finset.mem_filter]
  tauto

theorem exceptionalCoveredVertices_eq_biUnion (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D threshold : ℝ) :
    exceptionalCoveredVertices G C L D threshold =
      C.biUnion (largeResidualStarVertices G C L D threshold) := by
  exact Finset.filter_biUnion C (fun b => insert b (L b)) _

theorem exceptionalCoveredVertices_card_le (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D threshold : ℝ)
    (h : ∀ b ∈ C, (largeResidualStarVertices G C L D threshold b).card ≤ 1) :
    (exceptionalCoveredVertices G C L D threshold).card ≤ C.card := by
  rw [exceptionalCoveredVertices_eq_biUnion]
  calc
    _ ≤ ∑ b ∈ C, (largeResidualStarVertices G C L D threshold b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ C, 1 := Finset.sum_le_sum (fun b hb => h b hb)
    _ = C.card := by simp

theorem exceptionalCoveredVertices_size (G : SimpleGraph V) (k : ℕ) (C : Finset V)
    (L : V → Finset V) (D threshold : ℝ) (hF : IsGeneralStarForest G k C L)
    (h : ∀ b ∈ C, (largeResidualStarVertices G C L D threshold b).card ≤ 1) :
    k*(exceptionalCoveredVertices G C L D threshold).card ≤ Fintype.card V := by
  have hcount := exceptionalCoveredVertices_card_le G C L D threshold h
  calc
    _ ≤ k*C.card := Nat.mul_le_mul_left k hcount
    _ = (C.biUnion (fun b => insert b (L b))).card := hF.covered_card.symm
    _ ≤ Fintype.card V := Finset.card_le_univ _

omit [Fintype V] [DecidableEq V] in
theorem graphCrossingCount_comm (G : SimpleGraph V) (A B : Finset V) :
    graphCrossingCount G A B = graphCrossingCount G B A := by
  classical
  simp only [graphCrossingCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  rw [G.adj_comm]

theorem lowCovered_crossing_budget (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (D threshold : ℝ) (ht : 0 ≤ threshold) :
    (graphCrossingCount G (smallResidualVertices G C L D)
      ((C.biUnion (fun b => insert b (L b))) \ exceptionalCoveredVertices G C L D threshold):ℝ) ≤
      threshold*(C.biUnion (fun b => insert b (L b))).card := by
  classical
  rw [graphCrossingCount_comm]
  unfold graphCrossingCount
  rw [Nat.cast_sum]
  have hb : ∀ x ∈ (C.biUnion (fun b => insert b (L b))) \ exceptionalCoveredVertices G C L D threshold,
      (((smallResidualVertices G C L D).filter (G.Adj x)).card:ℝ) ≤ threshold := by
    intro x hx
    rw [← smallResidualNeighbors_eq_filter]
    have hxC := (Finset.mem_sdiff.mp hx).1
    have hxN := (Finset.mem_sdiff.mp hx).2
    exact (lt_of_not_ge (fun hh => hxN (Finset.mem_filter.mpr ⟨hxC,hh⟩))).le
  calc
    _ ≤ ∑ _x ∈ (C.biUnion (fun b => insert b (L b))) \ exceptionalCoveredVertices G C L D threshold,
      threshold := Finset.sum_le_sum hb
    _ = threshold*((C.biUnion (fun b => insert b (L b))) \ exceptionalCoveredVertices G C L D threshold).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)) ht

end MinorFreeSpanners
