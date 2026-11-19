import OnlineReachabilityPreservers.SteinerRate
import OnlineReachabilityPreservers.SteinerEarlyRound
import OnlineReachabilityPreservers.ThinSearchWork

/-! Magnitude bounds for the integers used by the two Steiner separators and rounding. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private theorem pow_two_of_log_bound {b k : ℕ} (positive : 0 < b) (level : k ≤ b.log2+1) :
    2^k ≤ 2*b := by
  calc
    _ ≤ 2^(b.log2+1) := Nat.pow_le_pow_right (by decide) level
    _ = 2*2^b.log2 := by rw [pow_succ']
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.log2_self_le positive.ne')

omit [Fintype V] in
private theorem augmentArcFlow_natAbs_le (f : ArcFlow V) (P : Arcs V) (e : V × V) :
    (augmentArcFlow f P e).natAbs ≤ (f e).natAbs+1 := by
  change (f e+(if e ∈ P then 1 else 0)-(if e.swap ∈ P then 1 else 0)).natAbs ≤ _
  by_cases a : e ∈ P <;> by_cases b : e.swap ∈ P
  · simp [a,b]
  · simpa [a,b] using Int.natAbs_add_le (f e) 1
  · simpa [a,b] using Int.natAbs_sub_le (f e) 1
  · simp [a,b]

/-- Every signed entry changes by at most one per successful augmentation,
including on the run that ultimately returns a small cut. -/
theorem unitAugmentations_entry_natAbs_le (c : ArcFlow V) (s t : V) (fuel B : ℕ)
    (f : ArcFlow V) (bounded : ∀ e, (f e).natAbs ≤ B) :
    let out := unitAugmentations c s t fuel f
    ∀ e, (out.1 e).natAbs ≤ B+out.2 := by
  induction fuel generalizing B f with
  | zero => simpa [unitAugmentations] using bounded
  | succ k ih =>
    cases route : routePath (residualArcs c f) s t with
    | none => simpa [unitAugmentations,route] using bounded
    | some path =>
      let after := augmentArcFlow f path.toFinset
      have next : ∀ e, (after e).natAbs ≤ B+1 :=
        fun e => (augmentArcFlow_natAbs_le f path.toFinset e).trans (Nat.succ_le_succ (bounded e))
      have step := ih (B+1) after next
      simp only [unitAugmentations, route]
      intro e
      change ((unitAugmentations c s t k after).1 e).natAbs ≤
        B+((unitAugmentations c s t k after).2+1)
      exact (step e).trans_eq (by omega)

theorem unitAugmentations_zero_entry_natAbs_le (c : ArcFlow V) (s t : V) (fuel : ℕ)
    (nonneg : ∀ e, 0 ≤ c e) (e : V × V) :
    ((unitAugmentations c s t fuel (fun _ => 0)).1 e).natAbs ≤ fuel := by
  have value := unitAugmentations_entry_natAbs_le c s t fuel 0 (fun _ => 0) (by simp) e
  exact (by simpa using value : ((unitAugmentations c s t fuel (fun _ => 0)).1 e).natAbs ≤
    (unitAugmentations c s t fuel (fun _ => 0)).2).trans (unitAugmentations_count fuel nonneg)

theorem thinCapacity_entry_le (G : Arcs V) (d : V × V) (load : CutLoads V)
    (bounded : ∀ e ∈ G, load e ≤ G.card.log2+1) (e : V × V) :
    0 ≤ localArcCapacity G d load e ∧ localArcCapacity G d load e ≤ (2*G.card : ℕ) := by
  unfold localArcCapacity
  split
  · rename_i inside
    have edge : e ∈ G := intervalArcs_subset _ _ inside
    have positive := card_pos.mpr ⟨e,edge⟩
    refine ⟨by positivity, ?_⟩
    exact_mod_cast pow_two_of_log_bound positive (bounded e edge)
  · exact ⟨le_rfl,by positivity⟩

omit [Fintype V] in
theorem weightedNetworkCapacity_entry_le (E : Arcs V) (d : WeightedNetworkDemand V)
    (weight charges : V × V → ℕ) (scale : ℕ) (positive : 0 < scale)
    (weightPositive : ∀ e ∈ E, 0 < weight e)
    (bound : ∀ e ∈ E, charges e ≤ (scale.log2+1)*weight e) (e : V × V) :
    0 ≤ weightedNetworkCapacity E d weight charges scale e ∧
      weightedNetworkCapacity E d weight charges scale e ≤ (4*scale+1 : ℕ) := by
  refine ⟨weightedNetworkCapacity_nonneg E d weight charges scale e,?_⟩
  unfold weightedNetworkCapacity
  split
  · exact_mod_cast (by omega : scale ≤ 4*scale+1)
  split
  · rename_i member
    exact_mod_cast roundedWeightedCapacity_le (weightPositive e member) positive (bound e member)
  · positivity

theorem forestMetricUnits_entry_le {height : ℕ} (G : Arcs V) (d : V × V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (bound : ∀ e ∈ forestNetworkPriced G (heightForest G height),
      charges e ≤ ((forestScale G height).log2+1)*forestNetworkWeight G e)
    (e : HeightForestVertex V height × HeightForestVertex V height) :
    forestMetricUnits G charges (forestScale G height) e ≤ 4*forestScale G height+1 := by
  let scale := forestScale G height
  let edges := forestNetworkPriced G (heightForest G height)
  have entry := (weightedNetworkCapacity_entry_le edges (forestNetworkDemand G height d)
    (forestNetworkWeight G) charges scale (forestScale_pos G height) (forestNetworkPriced_positive G _) bound
    (forestNetworkCopy.prodMap forestNetworkCopy e)).2
  rw [← forestMetricUnits_eq_capacity] at entry
  exact_mod_cast entry

/-- The numerator, denominator and comparison cutoff in a forest rounding
threshold have polynomial magnitude in the forest scale. -/
theorem forestHistoryRoundingOperands_le {scale height : ℕ} (positive : 0 < scale)
    (tier : Fin (scale.log2+1)) (units : HeightNode V height → ℕ) (v : HeightNode V height) :
    2^(scale.log2+1)*historyCapacityUnits tier.val units v ≤ 2*scale*scale ∧
      historyCapacityUnits tier.val units (heightParent v) ≤ scale ∧
      historyCutoff (scale.log2+1) tier.val units v ≤ 2*scale := by
  have tierBound : (2:ℕ)^tier.val ≤ scale :=
    (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ tier.isLt)).trans
      (Nat.log2_self_le positive.ne')
  have seedBound : (2:ℕ)^(scale.log2+1) ≤ 2*scale := pow_two_of_log_bound positive le_rfl
  refine ⟨Nat.mul_le_mul seedBound ((historyCapacityUnits_bounded _ _ _).trans tierBound),
    (historyCapacityUnits_bounded _ _ _).trans tierBound,
    (historyCutoff_bounded _ _ _ _).trans seedBound⟩

theorem steinerThinThreshold_le_vertices (n : ℕ) : steinerThinThreshold n ≤ n := by
  by_cases zero : n = 0
  · subst n
    decide
  · have positive := Nat.pos_of_ne_zero zero
    have n1 : (1:ℝ) ≤ n := by exact_mod_cast positive
    have h := (steinerThinThreshold_bounds positive).1.trans
      (Real.rpow_le_self_of_one_le n1 (show (3/5:ℝ) ≤ 1 by norm_num))
    exact_mod_cast h

/-- Thin rounding comparisons use an integer operand of at most this magnitude. -/
theorem thinPrefixRoundingOperand_le (G : Arcs V) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) (e : V × V) (member : e ∈ G) :
    let n := Fintype.card V
    thinRoundingFactor n (steinerThinThreshold n)*2^(thinCoverRun G D e) ≤ (5*n+4)*(2*G.card) := by
  let n := Fintype.card V
  obtain ⟨same,bounded,_,_⟩ := thinCoverRunWithSearchWork_spec G D feasible
  have cap : thinCoverRun G D e ≤ G.card.log2+1 := same ▸ bounded e member
  have pow : (2:ℕ)^(thinCoverRun G D e) ≤ 2*G.card :=
    pow_two_of_log_bound (card_pos.mpr ⟨e,member⟩) cap
  have factor : thinRoundingFactor n (steinerThinThreshold n) ≤ 5*n+4 := by
    unfold thinRoundingFactor
    have t := steinerThinThreshold_le_vertices n
    have l := Nat.log2_le_self n
    omega
  exact Nat.mul_le_mul factor pow

end OnlineReachabilityPreservers
