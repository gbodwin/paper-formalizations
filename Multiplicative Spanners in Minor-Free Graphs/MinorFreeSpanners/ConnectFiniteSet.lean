import MinorFreeSpanners.Minor
import MinorFreeSpanners.GreedyNeighborhoodCover

/-! Connect an actual finite set by a union of actual short walks. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- No connectivity certificate is assumed for the output set: its connecting
walks are built from prefixes of the supplied short walks in the host graph. -/
theorem connect_finite_set (G : SimpleGraph V) (L : ℕ)
    (hwalk : ∀ u v, ∃ p : G.Walk u v, p.length ≤ L)
    (B : Finset V) (hB : B.Nonempty) :
    ∃ C : Finset V, B ⊆ C ∧ C.card ≤ (L+1)*B.card ∧
      ∀ x ∈ C, ∀ y ∈ C, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ C := by
  classical
  obtain ⟨a,ha⟩ := hB
  choose p hp using hwalk a
  let C : Finset V := B.biUnion fun v => (p v).support.toFinset
  have hmem (v : V) (hv : v ∈ B) (z : V) (hz : z ∈ (p v).support) : z ∈ C := by
    exact Finset.mem_biUnion.mpr ⟨v,hv,List.mem_toFinset.mpr hz⟩
  refine ⟨C,?_,?_,?_⟩
  · intro v hv
    exact hmem v hv v (p v).end_mem_support
  · calc
      C.card ≤ ∑ v ∈ B, (p v).support.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ B, (L+1) := by
        apply Finset.sum_le_sum
        intro v _
        exact (List.toFinset_card_le _).trans (by simpa using Nat.succ_le_succ (hp v))
      _ = _ := by simp [Nat.mul_comm]
  · intro x hx y hy
    obtain ⟨v,hv,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨w,hw,hy⟩ := Finset.mem_biUnion.mp hy
    have hx' := List.mem_toFinset.mp hx
    have hy' := List.mem_toFinset.mp hy
    refine ⟨((p v).takeUntil x hx').reverse.append ((p w).takeUntil y hy'),?_⟩
    intro z hz
    rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
    · apply hmem v hv
      exact (p v).support_takeUntil_subset_support hx' (by simpa using hz)
    · exact hmem w hw z ((p w).support_takeUntil_subset_support hy' hz)

end MinorFreeSpanners
