import MinorFreeSpanners.StarSubfamilyQuotient
import MinorFreeSpanners.GeneralStarInsertion

/-! Actual original-vertex membership when one selected star is uncontracted
and a residual star is adjoined. These statements do not delete host vertices. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

theorem covered_mono_centers (C C' : Finset V) (L : V → Finset V) (h : C' ⊆ C) :
    C'.biUnion (fun b => insert b (L b)) ⊆ C.biUnion (fun b => insert b (L b)) := by
  intro x hx
  obtain ⟨c,hc,hx⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨c,h hc,hx⟩

variable [Fintype V]

theorem residual_mono_centers (C C' : Finset V) (L : V → Finset V) (h : C' ⊆ C) :
    starResidual C L ⊆ starResidual C' L := by
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
    fun hh => (Finset.mem_sdiff.mp hx).2 (covered_mono_centers C C' L h hh)⟩

theorem IsGeneralStarForest.erased_branch_residual {G : SimpleGraph V} {k : ℕ}
    {C : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L)
    {b x : V} (hb : b ∈ C) (hx : x ∈ insert b (L b)) :
    x ∈ starResidual (C.erase b) L := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ x,?_⟩
  intro hh
  obtain ⟨a,ha,hxa⟩ := Finset.mem_biUnion.mp hh
  exact Finset.disjoint_left.mp (h.2.2 a (Finset.mem_erase.mp ha).2 b hb
    (Finset.mem_erase.mp ha).1) hxa hx

omit [Fintype V] in
theorem covered_insert_of_old_leaves (C : Finset V) (L L' : V → Finset V) (c : V)
    (hold : ∀ b ∈ C, L' b=L b) :
    (insert c C).biUnion (fun b => insert b (L' b)) =
      insert c (L' c) ∪ C.biUnion (fun b => insert b (L b)) := by
  rw [Finset.biUnion_insert]
  congr 1
  apply Finset.biUnion_congr rfl
  intro b hb
  rw [hold b hb]

end MinorFreeSpanners
