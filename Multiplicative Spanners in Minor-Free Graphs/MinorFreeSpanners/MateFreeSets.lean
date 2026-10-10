import MinorFreeSpanners.PostleMates
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Actual common-neighbor control for the later star-branch construction.
This records deletion-monotonic mate-freeness, unlike global unmatedness,
whose small-vertex condition requires a separate argument after deletion. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

theorem common_neighbor_card_mono {G H : SimpleGraph V} (hHG : H ≤ G) (x y : V) :
    Fintype.card (H.commonNeighbors x y) ≤ Fintype.card (G.commonNeighbors x y) :=
  Set.card_le_card (fun _ h => ⟨hHG h.1,hHG h.2⟩)

/-- No distinct pair in S has as many as q actual common neighbors. -/
def MateFreeOn (G : SimpleGraph V) (q : ℝ) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (Fintype.card (G.commonNeighbors x y):ℝ) < q

theorem MateFreeOn.mono {G H : SimpleGraph V} {q : ℝ} {S : Set V}
    (h : MateFreeOn G q S) (hHG : H ≤ G) : MateFreeOn H q S := by
  intro x hx y hy hxy
  exact (Nat.cast_le.mpr (common_neighbor_card_mono hHG x y)).trans_lt (h x hx y hy hxy)

theorem MateFreeOn.subset {G : SimpleGraph V} {q : ℝ} {S T : Set V}
    (h : MateFreeOn G q S) (hTS : T ⊆ S) : MateFreeOn G q T :=
  fun x hx y hy hxy => h x (hTS hx) y (hTS hy) hxy

/-- Opposite sides of a bipartite graph have no common neighbor. -/
theorem bipartite_commonNeighbors_empty (G : SimpleGraph V) {A B : Set V}
    (hG : G.IsBipartiteWith A B) {x y : V} (hx : x ∈ A) (hy : y ∈ B) :
    G.commonNeighbors x y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact Set.disjoint_left.mp hG.disjoint
    (hG.mem_of_mem_adj' hy hz.2.symm) (hG.mem_of_mem_adj hx hz.1)

/-- Adjoining a star center from the other side preserves mate-freeness
of a set of leaves, for a positive common-neighbor threshold. -/
theorem MateFreeOn.insert_center {G : SimpleGraph V} {q : ℝ} {A B L : Set V}
    (hG : G.IsBipartiteWith A B) (hL : L ⊆ A) (h : MateFreeOn G q L)
    (hq : 0 < q) {b : V} (hb : b ∈ B) : MateFreeOn G q (insert b L) := by
  classical
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hxy (hx.trans hy.symm)).elim
  · have he := bipartite_commonNeighbors_empty G hG (hL hy) hb
    subst x
    have hc : Fintype.card (G.commonNeighbors b y) = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun z => by simpa [G.commonNeighbors_symm b y,he] using z.property⟩
    simpa only [hc,Nat.cast_zero] using hq
  · subst y
    have he := bipartite_commonNeighbors_empty G hG (hL hx) hb
    have hc : Fintype.card (G.commonNeighbors x b) = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun z => by simpa [he] using z.property⟩
    simpa only [hc,Nat.cast_zero] using hq
  · exact h x hx y hy hxy

end MinorFreeSpanners
