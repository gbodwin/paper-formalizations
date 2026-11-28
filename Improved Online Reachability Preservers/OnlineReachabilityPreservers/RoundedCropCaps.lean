import OnlineReachabilityPreservers.HalfFiveRoundedLowerCaps
import OnlineReachabilityPreservers.HalfSixStartingLowerCaps

/-! Recover exact starting caps from the pruned mass and integer thresholds. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- The discarded integer degree and length thresholds, plus the largest
integer mass below the target, must lie strictly below the crop bound. -/
def frozenCropChargeFits (n p M K r : ℕ) : Prop :=
  (frozenLowerPeelCharge n p M : ℝ)+(((M-1)/r : ℕ):ℝ) < halfPrunedCropScore M K

/-- A nonstrict bound on the integer removal charge already gives
retention `M/930` from a pruned family keeping half the mass. -/
theorem frozen_crop_charge_fits_of_coarse_charge {n p M K : ℕ} (positive : 0 < M)
    (pruned : M ≤ 2*K) (upper : K ≤ M)
    (charge : 15*frozenLowerPeelCharge n p M ≤ 7*M) : frozenCropChargeFits n p M K 930 := by
  let C := frozenLowerPeelCharge n p M
  let z := (M-1)/930
  have lower := half_pruned_crop_score_of_half_mass positive pruned upper
  have fee : 15*(C:ℝ) ≤ 7*(M:ℝ) := by exact_mod_cast charge
  have floor : z*930 ≤ M-1 := Nat.div_mul_le_self _ _
  have room : (z:ℝ)*930 < (M:ℝ) := by exact_mod_cast (show z*930 < M by omega)
  change (C:ℝ)+(z:ℝ) < halfPrunedCropScore M K
  linarith only [fee,room,lower]

/-- After safe width splitting, the integer charge criterion gives all
four exact starting caps at the selected half cutoff. -/
theorem regularization_list_frozen_half_of_integer_crop_charge {n p k r : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (cutoff : 3 ≤ k)
    (splitSafe : let M := ∑ i, (paths i).length
      HalfBridgeFree (Before (listRegularizedPaths (removeOppositeIntersections paths) (4*M/n) (4*M/p))) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retention : 8 ≤ r)
    (room : frozenCropChargeFits n p (∑ i, (paths i).length)
      (∑ i, (removeOppositeIntersections paths i).length) r) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) k ∧
      M ≤ r*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  let K := ∑ i, (removeOppositeIntersections paths i).length
  let C := frozenLowerPeelCharge n p M
  let z := (M-1)/r
  let dn := ((n:ℝ)*(((M-1)/(4*n):ℕ):ℝ))/(M:ℝ)
  let lp := ((p:ℝ)*(((M-1)/(4*p):ℕ):ℝ))/(M:ℝ)
  have mPos : 0 < M := hn.trans_le dense
  have rm : (0:ℝ) < M := by exact_mod_cast mPos
  have rPos : 0 < r := by omega
  have rr : (0:ℝ) < r := by exact_mod_cast rPos
  have rLarge : (8:ℝ) ≤ r := by exact_mod_cast (show 8 ≤ r by omega)
  have zBelow : (z:ℝ) < (M:ℝ)/r := by
    apply (lt_div_iff₀ rr).mpr
    have mulBound : z*r ≤ M-1 := Nat.div_mul_le_self _ _
    exact_mod_cast (show z*r < M by omega)
  obtain ⟨dn0,dnTop,degree⟩ := frozen_lower_fraction_interval mPos hn
  obtain ⟨lp0,lpTop,row⟩ := frozen_lower_fraction_interval mPos hp
  change 0 ≤ dn at dn0
  change dn < 1/4 at dnTop
  change 0 ≤ lp at lp0
  change lp < 1/4 at lpTop
  change (C:ℝ)+(z:ℝ) < halfPrunedCropScore M K at room
  let ε := min ((halfPrunedCropScore M K - C - z)/4)
    (min (((M:ℝ)/r-z)/2) (min ((1/4-dn)*(M:ℝ)/2) ((1/4-lp)*(M:ℝ)/2)))
  have epsPos : 0 < ε := by
    apply lt_min (by linarith only [room])
    exact lt_min (by linarith only [zBelow])
      (lt_min (div_pos (mul_pos (sub_pos.mpr dnTop) rm) (by norm_num))
        (div_pos (mul_pos (sub_pos.mpr lpTop) rm) (by norm_num)))
  have budget : ε ≤ (halfPrunedCropScore M K-C-z)/4 := min_le_left _ _
  have massRoom : ε ≤ ((M:ℝ)/r-z)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have degreeRoom : ε ≤ (1/4-dn)*(M:ℝ)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have rowRoom : ε ≤ (1/4-lp)*(M:ℝ)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let a := dn+ε/(M:ℝ)
  let b := lp+ε/(M:ℝ)
  let target := (z:ℝ)+ε
  have deltaPos := div_pos epsPos rm
  have degreeGap : ε/(M:ℝ) ≤ (1/4-dn)/2 := (div_le_iff₀ rm).mpr (by linarith only [degreeRoom])
  have pathGap : ε/(M:ℝ) ≤ (1/4-lp)/2 := (div_le_iff₀ rm).mpr (by linarith only [rowRoom])
  have a0 : 0 ≤ a := add_nonneg dn0 deltaPos.le
  have b0 : 0 ≤ b := add_nonneg lp0 deltaPos.le
  have aMax : a ≤ 1/4 := by dsimp only [a]; linarith only [degreeGap, dnTop]
  have bMax : b ≤ 1/4 := by dsimp only [b]; linarith only [pathGap, lpTop]
  have targetFit : target ≤ (M:ℝ)/8 := calc
    _ ≤ (M:ℝ)/r := by dsimp only [target]; linarith only [massRoom,zBelow]
    _ ≤ _ := div_le_div_of_nonneg_left rm.le (by norm_num) rLarge
  have basePrice : (dn+lp)*(M:ℝ) = C := by
    dsimp only [dn,lp,C,frozenLowerPeelCharge]
    rw [add_mul,div_mul_cancel₀ _ rm.ne',div_mul_cancel₀ _ rm.ne']
    push_cast
    rfl
  have price : (a+b)*(M:ℝ)+target = (C:ℝ)+(z:ℝ)+3*ε := by
    have sum : a+b = (dn+lp)+2*(ε/(M:ℝ)) := by dsimp only [a,b]; ring
    rw [sum,add_mul,basePrice,mul_assoc,div_mul_cancel₀ _ rm.ne']
    dsimp only [target]
    ring
  have enough : (a+b)*(M:ℝ)+target ≤ halfPrunedCropScore M K := by
    rw [price]
    linarith only [budget,epsPos]
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,keep,upper,degrees,lengths⟩ :=
    regularization_list_half_of_starting_lower_caps_and_mass paths simple free cutoff splitSafe hn hp dense long
      a0 b0 aMax bMax targetFit enough
  have above : (z:ℝ) < ((∑ i, (rows i).length : ℕ):ℝ) := (lt_add_of_pos_right _ epsPos).trans_le keep
  have occupied : z < ∑ i, (rows i).length := by exact_mod_cast above
  have retain : M ≤ r*(∑ i, (rows i).length) := by
    have threshold : M-1 < (∑ i, (rows i).length)*r := (Nat.div_lt_iff_lt_mul rPos).mp occupied
    rw [Nat.mul_comm] at threshold
    omega
  have aboveDegree : dn < a := lt_add_of_pos_right _ deltaPos
  have abovePath : lp < b := lt_add_of_pos_right _ deltaPos
  exact ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,
    fun v => ⟨degree aboveDegree (degrees v).1,(degrees v).2⟩,
    fun i => ⟨row abovePath (lengths i).1,(lengths i).2⟩⟩

/-- The integer criterion also supplies a distinct, nonempty witness
from distinct nonempty input. -/
theorem regularization_literal_frozen_half_of_integer_crop_charge {n p k r : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (cutoff : 3 ≤ k)
    (splitSafe : let M := ∑ i, (paths i).length
      HalfBridgeFree (Before (listRegularizedPaths (removeOppositeIntersections paths) (4*M/n) (4*M/p))) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (retention : 8 ≤ r)
    (room : frozenCropChargeFits n p (∑ i, (paths i).length)
      (∑ i, (removeOppositeIntersections paths i).length) r) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) k ∧
      M ≤ r*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,full,keep,upper,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid free (by omega) hn hp dense low
    exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,(full k).halfFree,
      keep.trans (Nat.mul_le_mul_right _ (by omega)),upper,caps⟩
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun i _ => List.length_pos_of_ne_nil (valid i).1)
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,keep,upper,caps⟩ :=
    regularization_list_frozen_half_of_integer_crop_charge paths (fun i => (valid i).2)
      free cutoff splitSafe hn hp dense long retention room
  have mean : 4*p < M := by have bound := le_max_right n p; omega
  obtain ⟨oneToOne,nonempty⟩ :=
    frozen_length_distinct_of_large_mean rowsSimple rowsFree (by omega) hp mean caps
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,rowsSimple i⟩,rowsFree,keep,upper,caps⟩

/-- The integer crop test gives exact starting caps at half cutoff five. -/
theorem regularization_list_frozen_half_five_of_integer_crop_charge {n p r : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retention : 8 ≤ r)
    (room : frozenCropChargeFits n p (∑ i, (paths i).length)
      (∑ i, (removeOppositeIntersections paths i).length) r) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ r*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  exact regularization_list_frozen_half_of_integer_crop_charge paths simple free (by decide)
    (listRegularizedPaths_halfFree_five_after_opposite_pruning paths simple free)
    hn hp dense long retention room

/-- The integer crop test gives exact starting caps at half cutoff five, for distinct nonempty input and output. -/
theorem regularization_literal_frozen_half_five_of_integer_crop_charge {n p r : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    (retention : 8 ≤ r)
    (room : frozenCropChargeFits n p (∑ i, (paths i).length)
      (∑ i, (removeOppositeIntersections paths i).length) r) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
      HalfBridgeFree (Before rows) 5 ∧ M ≤ r*(∑ i, (rows i).length) ∧
      (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  exact regularization_literal_frozen_half_of_integer_crop_charge paths distinct valid free (by decide)
    (listRegularizedPaths_halfFree_five_after_opposite_pruning paths (fun i => (valid i).2) free)
    hn hp dense retention room

/-- The integer crop test gives exact starting caps at half cutoff six
with full-three exclusion. -/
theorem regularization_list_frozen_half_six_of_integer_crop_charge {n p r : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retention : 8 ≤ r)
    (room : frozenCropChargeFits n p (∑ i, (paths i).length)
      (∑ i, (removeOppositeIntersections paths i).length) r) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 6 ∧
      M ≤ r*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  exact regularization_list_frozen_half_of_integer_crop_charge paths simple free (by decide)
    (listRegularizedPaths_halfFree_six_after_opposite_pruning paths simple free three)
    hn hp dense long retention room

/-- The integer crop test gives exact starting caps at half cutoff six
with full-three exclusion, for distinct nonempty input and output. -/
theorem regularization_literal_frozen_half_six_of_integer_crop_charge {n p r : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    (retention : 8 ≤ r)
    (room : frozenCropChargeFits n p (∑ i, (paths i).length)
      (∑ i, (removeOppositeIntersections paths i).length) r) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
      HalfBridgeFree (Before rows) 6 ∧ M ≤ r*(∑ i, (rows i).length) ∧
      (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  exact regularization_literal_frozen_half_of_integer_crop_charge paths distinct valid free (by decide)
    (listRegularizedPaths_halfFree_six_after_opposite_pruning paths (fun i => (valid i).2) free three)
    hn hp dense retention room

end OnlineReachabilityPreservers
