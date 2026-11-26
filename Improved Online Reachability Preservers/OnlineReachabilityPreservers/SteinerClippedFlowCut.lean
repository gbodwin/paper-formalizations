import OnlineReachabilityPreservers.SteinerCutFlow

/-! Capacity clipping preserves the complete bounded separator response. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- A bounded cut query returns the same answer after clipping every
nonnegative capacity to its supply, including the exact source side. -/
theorem findLowCapacityCut_clip_to_supply (capacity : ArcFlow V) (source target : V) (supply : ℕ)
    (nonnegative : ∀ e, 0 ≤ capacity e) :
    findLowCapacityCut (fun e => min (capacity e) (supply : ℤ)) source target supply =
      findLowCapacityCut capacity source target supply := by
  let clipped : ArcFlow V := fun e => min (capacity e) (supply : ℤ)
  let run := unitAugmentations clipped source target supply (fun _ => 0)
  let side := residualReach clipped run.1 source
  have clippedNonnegative (e : V × V) : 0 ≤ clipped e :=
    le_min (nonnegative e) (Int.natCast_nonneg _)
  have below (e : V × V) : clipped e ≤ capacity e := min_le_left _ _
  obtain ⟨valid,count,stalled⟩ := unitAugmentations_zero_spec clipped source target supply clippedNonnegative
  change ValidArcFlow clipped source target run.2 run.1 at valid
  change run.2 ≤ supply at count
  change run.2 < supply → ¬ Reach (residualArcs clipped run.1) source target at stalled
  have originalValid : ValidArcFlow capacity source target run.2 run.1 :=
    ⟨valid.skew,fun e => (valid.upper e).trans (below e),valid.balance⟩
  have observed : findLowCapacityCut clipped source target supply =
      if run.2 = supply then none else some side := rfl
  change findLowCapacityCut clipped source target supply = _
  rw [observed]
  by_cases enough : run.2 = supply
  · rw [findLowCapacityCut_eq_terminal nonnegative originalValid count (fun small => (small.ne enough).elim)]
    simp only [enough,ite_true]
  · have short : run.2 < supply := lt_of_le_of_ne count enough
    have found : findLowCapacityCut clipped source target supply = some side := by
      rw [observed,ite_eq_right enough]
    have proof := findLowCapacityCut_spec clipped source target supply clippedNonnegative
    rw [found] at proof
    obtain ⟨start,finish,capacitySmall⟩ := proof
    have unchanged {u v : V} (inside : u ∈ side) (outside : v ∉ side) : clipped (u,v) = capacity (u,v) := by
      have crossing : (u,v) ∈ side ×ˢ sideᶜ := mem_product.mpr ⟨inside,mem_compl.mpr outside⟩
      have single : clipped (u,v) ≤ ∑ e ∈ side ×ˢ sideᶜ, clipped e :=
        single_le_sum (fun e _ => clippedNonnegative e) crossing
      rw [sum_product side sideᶜ clipped] at single
      change clipped (u,v) ≤ cutArcFlow clipped side at single
      have small := single.trans_lt capacitySmall
      change min (capacity (u,v)) (supply : ℤ) < (supply : ℤ) at small
      have belowSupply : capacity (u,v) ≤ (supply : ℤ) := by
        by_contra! larger
        rw [min_eq_right larger.le] at small
        exact (lt_irrefl _ small)
      exact min_eq_left belowSupply
    have closed {u v : V} (inside : u ∈ side) (edge : Edge (residualArcs capacity run.1) u v) : v ∈ side := by
      by_contra! outside
      have residual : Edge (residualArcs clipped run.1) u v := by
        refine mem_filter.mpr ⟨mem_univ _,?_⟩
        rw [unchanged inside outside]
        exact (mem_filter.mp edge).2
      exact outside (mem_residualReach.mpr ((mem_residualReach.mp inside).tail residual))
    have stays {v : V} (reach : Reach (residualArcs capacity run.1) source v) : v ∈ side := by
      induction reach with
      | refl => exact start
      | tail _ edge ih => exact closed ih edge
    have sameSide : residualReach capacity run.1 source = side := by
      apply Subset.antisymm
      · exact fun _ h => stays (mem_residualReach.mp h)
      · intro v inside
        have sub : residualArcs clipped run.1 ⊆ residualArcs capacity run.1 := by
          intro e available
          exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp available).2.trans_le (below e)⟩
        exact mem_residualReach.mpr (reach_mono sub (mem_residualReach.mp inside))
    have originalStalled : ¬ Reach (residualArcs capacity run.1) source target := fun route => finish (stays route)
    rw [findLowCapacityCut_eq_terminal nonnegative originalValid count (fun _ => originalStalled)]
    simp only [enough,ite_false,sameSide]

end OnlineReachabilityPreservers
