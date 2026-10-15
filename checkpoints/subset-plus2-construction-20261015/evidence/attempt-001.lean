import SlackSparsification.SubsetPlusTwoClustering

namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A finite maximal star packing; maximality is used only for residual degree. -/
structure StarPacking (G : SimpleGraph V) (d : ℕ) where
  clusters : Finset (Finset V)
  disjoint : ∀ C ∈ clusters, ∀ D ∈ clusters, C ≠ D → Disjoint C D
  size : ∀ C ∈ clusters, C.card = d
  star : ∀ C ∈ clusters, ∃ c, ∀ v ∈ C, G.Adj v c
  residual : ∀ c, ((G.neighborFinset c) \ clusters.biUnion id).card < d

/-- Existence includes empty vertex types and parameters larger than the graph. -/
theorem exists_starPacking (G : SimpleGraph V) (d : ℕ) (hd : 0 < d) :
    Nonempty (StarPacking G d) := by
  let valid := fun Cs : Finset (Finset V) =>
    (∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) ∧
    (∀ C ∈ Cs, C.card = d) ∧ (∀ C ∈ Cs, ∃ c, ∀ v ∈ C, G.Adj v c)
  let candidates := univ.filter valid
  have hempty : ∅ ∈ candidates := by simp [candidates, valid]
  obtain ⟨Cs, hCs, hmax⟩ := exists_max_image candidates Finset.card ⟨∅, hempty⟩
  obtain ⟨hdisj, hsize, hstar⟩ := (mem_filter.mp hCs).2
  refine ⟨⟨Cs, hdisj, hsize, hstar, ?_⟩⟩
  intro c
  by_contra hlt
  obtain ⟨C, hsub, hcard⟩ := exists_subset_card_eq (by omega : d ≤ ((G.neighborFinset c) \ Cs.biUnion id).card)
  have hnew : C ∉ Cs := by
    intro hc
    obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < C.card)
    exact (mem_sdiff.mp (hsub hv)).2 (mem_biUnion.mpr ⟨C, hc, hv⟩)
  have hdC : ∀ D ∈ Cs, Disjoint C D := by
    intro D hD
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    exact (mem_sdiff.mp (hsub hv)).2 (mem_biUnion.mpr ⟨D, hD, hvD⟩)
  have hvalid : valid (insert C Cs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro A hA B hB hne
      rcases mem_insert.mp hA with rfl | hA
      · rcases mem_insert.mp hB with rfl | hB
        · exact (hne rfl).elim
        · exact hdC B hB
      · rcases mem_insert.mp hB with rfl | hB
        · exact (hdC A hA).symm
        · exact hdisj A hA B hB hne
    · intro A hA
      rcases mem_insert.mp hA with rfl | hA
      · exact hcard
      · exact hsize A hA
    · intro A hA
      rcases mem_insert.mp hA with rfl | hA
      · exact ⟨c, fun v hv => (mem_neighborFinset.mp (mem_sdiff.mp (hsub hv)).1).symm⟩
      · exact hstar A hA
  have hb := hmax (insert C Cs) (mem_filter.mpr ⟨mem_univ _, hvalid⟩)
  rw [card_insert_of_notMem hnew] at hb
  omega

end SlackSparsification.SubsetPlusTwo
