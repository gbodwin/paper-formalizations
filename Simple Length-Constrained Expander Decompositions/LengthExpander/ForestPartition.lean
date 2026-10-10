import LengthExpander.ForestCover

namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} {K : ℕ}

/-- Keep each edge only in its earliest covering forest. -/
def firstForest (F : Fin K → SimpleGraph V) (i : Fin K) : SimpleGraph V where
  Adj u v := (F i).Adj u v ∧ ∀ j, j < i → ¬(F j).Adj u v
  symm.symm _ _ h := ⟨h.1.symm,fun j hj hadj => h.2 j hj hadj.symm⟩
  loopless.irrefl _ h := h.1.ne rfl

theorem firstForest_le (F : Fin K → SimpleGraph V) (i : Fin K) :
    firstForest F i ≤ F i := fun _ _ h => h.1

/-- Any finite forest cover can be pruned to an actual edge partition without
increasing the number of forests. This includes the zero-forest empty graph. -/
theorem partition_of_forest_cover {G : SimpleGraph V} (F : Fin K → SimpleGraph V)
    (ha : ∀ i, (F i).IsAcyclic) (hle : ∀ i, F i ≤ G)
    (hc : ∀ u v, G.Adj u v → ∃ i, (F i).Adj u v) :
    ∃ P : Fin K → SimpleGraph V, (∀ i, (P i).IsAcyclic) ∧
      (∀ i, P i ≤ G) ∧ (∀ u v, G.Adj u v → ∃! i, (P i).Adj u v) := by
  classical
  refine ⟨firstForest F,fun i => (ha i).anti (firstForest_le F i),
    fun i => (firstForest_le F i).trans (hle i),?_⟩
  intro u v huv
  let T := univ.filter (fun i : Fin K => (F i).Adj u v)
  have hT : T.Nonempty := by
    obtain ⟨i,hi⟩ := hc u v huv
    exact ⟨i,mem_filter.mpr ⟨mem_univ i,hi⟩⟩
  let i := T.min' hT
  have hi : (firstForest F i).Adj u v := by
    refine ⟨(mem_filter.mp (T.min'_mem hT)).2,?_⟩
    intro j hj hjuv
    have hjT : j ∈ T := mem_filter.mpr ⟨mem_univ j,hjuv⟩
    exact (not_lt_of_ge (T.min'_le j hjT)) hj
  refine ⟨i,hi,?_⟩
  intro j hj
  rcases lt_trichotomy j i with hlt | heq | hgt
  · exact (hi.2 j hlt hj.1).elim
  · exact heq
  · exact (hj.2 i hgt hi.1).elim

variable [Fintype V] {G : SimpleGraph V}

/-- Explicit, fully constructed forest-partition version of Theorem 1.3. -/
theorem parallelGreedy_forest_partition {index : Sym2 V → ℕ} {s : ℕ}
    (H : IsParallelGreedy G index s) (hs : 2 ≤ s) :
    ∃ P : Fin (densityBudget (Fintype.card V) s) → SimpleGraph V,
      (∀ i, (P i).IsAcyclic) ∧ (∀ i, P i ≤ G) ∧
      (∀ u v, G.Adj u v → ∃! i, (P i).Adj u v) := by
  obtain ⟨F,ha,hle,hc⟩ := parallelGreedy_forest_cover H hs
  exact partition_of_forest_cover F ha hle hc

end LengthExpander
