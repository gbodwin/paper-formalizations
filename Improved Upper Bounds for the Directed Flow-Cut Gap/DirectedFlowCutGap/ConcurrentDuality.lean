import DirectedFlowCutGap.ConcurrentProfiles
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

/-!
# Attained concurrent-flow / normalized fractional-sparsest duality

Distances below are certified by lower bounds on every actual path and an
actual minimizing path. They are therefore distances, not freely chosen dual
variables. Joint-profile covering is exactly the constraint that the sum of
these distances is at least one. A positive normalization witness is the only
feasibility input; neither an optimizer nor LP duality is assumed.

The resulting optimum has distance sum one. A separate average normalization
rescales to the number of demands, preserving the ratio and making the correct
mass parameter explicit. Zero capacities and zero optimal objective are allowed.
-/

namespace DirectedFlowCutGap.ConcurrentDuality
noncomputable section
open scoped BigOperators
open ConcurrentProfiles
attribute [local instance] Classical.propDecidable

variable {R D : Type*} [Fintype R] [Fintype D]
variable {Path : D → Type*} [∀ d, Fintype (Path d)]

/-- Length of one actual path, with its full incidence multiplicity. -/
def pathWeight (a : ∀ d, R → Path d → ℕ) (w : R → ℝ) (d : D) (p : Path d) : ℝ :=
  ∑ r, (a d r p : ℝ) * w r

/-- The distance is attained and is a lower bound for every actual path. -/
def IsDistance (a : ∀ d, R → Path d → ℕ) (w : R → ℝ) (dist : D → ℝ) : Prop :=
  ∀ d, (∀ p, dist d ≤ pathWeight a w d p) ∧ ∃ p, pathWeight a w d p = dist d

/-- Capacity-weighted fractional objective. -/
abbrev cost (c w : R → ℝ) : ℝ := IntegerPackingCovering.coveringValue c w

omit [Fintype D] in
/-- Attainment uses finite minimization, with reachability explicitly required. -/
theorem exists_distances (a : ∀ d, R → Path d → ℕ) (w : R → ℝ)
    [∀ d, Nonempty (Path d)] : ∃ dist, IsDistance a w dist := by
  classical
  have hm : ∀ d, ∃ p : Path d, ∀ q, pathWeight a w d p ≤ pathWeight a w d q :=
    fun d => Finite.exists_min (pathWeight a w d)
  choose p hp using hm
  exact ⟨fun d => pathWeight a w d (p d), fun d => ⟨hp d, p d, rfl⟩⟩

omit [Fintype D] [∀ d, Fintype (Path d)] in
/-- Actual attained shortest-path distances are unique. -/
theorem distances_unique {a : ∀ d, R → Path d → ℕ} {w : R → ℝ}
    {dist dist' : D → ℝ} (hd : IsDistance a w dist) (hd' : IsDistance a w dist') :
    dist = dist' := by
  funext d
  obtain ⟨p, hp⟩ := (hd d).2
  obtain ⟨q, hq⟩ := (hd' d).2
  exact le_antisymm (by simpa [hq] using (hd d).1 q)
    (by simpa [hp] using (hd' d).1 p)

omit [Fintype D] [∀ d, Fintype (Path d)] in
/-- Every demanded distance is nonnegative for nonnegative lengths. -/
theorem distances_nonneg {a : ∀ d, R → Path d → ℕ} {w : R → ℝ} {dist : D → ℝ}
    (hw : ∀ r, 0 ≤ w r) (hd : IsDistance a w dist) (d : D) : 0 ≤ dist d := by
  obtain ⟨p, hp⟩ := (hd d).2
  rw [← hp]
  exact Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg _) (hw r)

omit [∀ d, Fintype (Path d)] in
/-- The profile weight is the sum of the weights of its constituent paths. -/
theorem profileWeight_eq (a : ∀ d, R → Path d → ℕ) (w : R → ℝ) (q : Profile Path) :
    IntegerPackingCovering.pathWeight (profileIncidence a) w q = ∑ d, pathWeight a w d (q d) := by
  simp only [IntegerPackingCovering.pathWeight, profileIncidence, pathWeight,
    Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

omit [∀ d, Fintype (Path d)] in
/-- Exact dual constraint: all joint paths have length at least one iff the sum of
actual demanded distances is at least one. -/
theorem covering_iff_distanceSum {a : ∀ d, R → Path d → ℕ} {w : R → ℝ} {dist : D → ℝ}
    (hd : IsDistance a w dist) :
    IntegerPackingCovering.IsCovering (profileIncidence a) w ↔
      (∀ r, 0 ≤ w r) ∧ 1 ≤ ∑ d, dist d := by
  classical
  constructor
  · intro hw
    choose p hp using fun d => (hd d).2
    refine ⟨hw.1, ?_⟩
    have h := hw.2 p
    rw [profileWeight_eq] at h
    simpa only [hp] using h
  · rintro ⟨hw, hs⟩
    refine ⟨hw, fun q => ?_⟩
    rw [profileWeight_eq]
    exact hs.trans (Finset.sum_le_sum fun d _ => (hd d).1 (q d))

omit [Fintype D] [∀ d, Fintype (Path d)] in
/-- Exact scaling includes every individual distance, including zero ones. -/
theorem distance_scale {a : ∀ d, R → Path d → ℕ} {w : R → ℝ} {dist : D → ℝ}
    (hd : IsDistance a w dist) {s : ℝ} (hs : 0 ≤ s) :
    IsDistance a (fun r => s * w r) (fun d => s * dist d) := by
  have heq (d : D) (p : Path d) : pathWeight a (fun r => s * w r) d p =
      s * pathWeight a w d p := by
    simp [pathWeight, Finset.mul_sum, mul_left_comm]
  intro d
  refine ⟨fun p => ?_, ?_⟩
  · rw [heq]
    exact mul_le_mul_of_nonneg_left ((hd d).1 p) hs
  · obtain ⟨p, hp⟩ := (hd d).2
    exact ⟨p, by rw [heq, hp]⟩

omit [Fintype D] [∀ d, Fintype (Path d)] in
theorem cost_scale (c w : R → ℝ) (s : ℝ) :
    cost c (fun r => s * w r) = s * cost c w := by
  simp [cost, IntegerPackingCovering.coveringValue, Finset.mul_sum, mul_left_comm]

omit [∀ d, Fintype (Path d)] in
/-- Every positive distance sum produces a feasible sum-one cover. -/
theorem normalized_covering {a : ∀ d, R → Path d → ℕ} {w : R → ℝ} {dist : D → ℝ}
    (hw : ∀ r, 0 ≤ w r) (hd : IsDistance a w dist) (hs : 0 < ∑ d, dist d) :
    IntegerPackingCovering.IsCovering (profileIncidence a)
      (fun r => (1 / (∑ d, dist d)) * w r) := by
  apply (covering_iff_distanceSum (distance_scale hd (by positivity : 0 ≤ 1 / (∑ d, dist d)))).mpr
  refine ⟨fun r => mul_nonneg (by positivity) (hw r), ?_⟩
  simp [← Finset.mul_sum, hs.ne']

omit [∀ d, Fintype (Path d)] in
/-- Positive-normalization feasibility excludes a zero-resource joint profile. -/
theorem positive_profile_of_covering {a : ∀ d, R → Path d → ℕ} {w : R → ℝ}
    (hw : IntegerPackingCovering.IsCovering (profileIncidence a) w) :
    ∀ q : Profile Path, ∃ r, 0 < profileIncidence a r q := by
  intro q
  by_contra h
  push Not at h
  have hz : ∀ r, profileIncidence a r q = 0 := fun r => Nat.eq_zero_of_le_zero (h r)
  have hh := hw.2 q
  norm_num [IntegerPackingCovering.pathWeight, hz] at hh

/-- The exact feasible normalized domain, allowing some free demands. -/
theorem positive_normalization_iff (a : ∀ d, R → Path d → ℕ)
    [∀ d, Nonempty (Path d)] :
    (∃ w dist, (∀ r, 0 ≤ w r) ∧ IsDistance a w dist ∧ 0 < ∑ d, dist d) ↔
      ∀ q : Profile Path, ∃ r, 0 < profileIncidence a r q := by
  constructor
  · rintro ⟨w, dist, hw, hd, hs⟩
    exact positive_profile_of_covering (normalized_covering hw hd hs)
  · intro h
    obtain ⟨dist, hd⟩ := exists_distances a (fun _ => 1)
    have hw := IntegerPackingCovering.one_isCovering (profileIncidence a) h
    have hs := ((covering_iff_distanceSum hd).mp hw).2
    exact ⟨(fun _ => 1), dist, fun _ => zero_le_one, hd, zero_lt_one.trans_le hs⟩

omit [∀ d, Fintype (Path d)] in
/-- A free joint profile makes every finite demanded-distance sum zero. -/
theorem distanceSum_eq_zero_of_free_profile {a : ∀ d, R → Path d → ℕ}
    {w : R → ℝ} {dist : D → ℝ} (hw : ∀ r, 0 ≤ w r) (hd : IsDistance a w dist)
    (q : Profile Path) (hq : ∀ r, profileIncidence a r q = 0) :
    (∑ d, dist d) = 0 := by
  apply le_antisymm _ (Finset.sum_nonneg fun d _ => distances_nonneg hw hd d)
  calc
    (∑ d, dist d) ≤ ∑ d, pathWeight a w d (q d) :=
      Finset.sum_le_sum fun d _ => (hd d).1 (q d)
    _ = IntegerPackingCovering.pathWeight (profileIncidence a) w q :=
      (profileWeight_eq a w q).symm
    _ = 0 := by simp [IntegerPackingCovering.pathWeight, hq]

omit [Fintype R] in
/-- The free-profile case is truly unbounded, including empty demand families. -/
theorem concurrent_unbounded_of_free_profile (a : ∀ d, R → Path d → ℕ)
    {c : R → ℝ} (hc : ∀ r, 0 ≤ c r) (q : Profile Path)
    (hq : ∀ r, profileIncidence a r q = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ f, IsConcurrent a c f t := by
  classical
  apply (concurrent_iff_profile_packing a hc t).mpr
  refine ⟨Pi.single q t, ⟨?_, ?_⟩, ?_⟩
  · intro q'
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  · intro r
    simpa [IntegerPackingCovering.load, Pi.single_apply, hq] using hc r
  · simp [IntegerPackingCovering.packingValue]

/-- An optimizer contains the actual flow, length assignment and attained
path distances. Optimality concerns all feasible conventional concurrent flows
and all positive-denominator fractional assignments. -/
structure Solution (a : ∀ d, R → Path d → ℕ) (c : R → ℝ) where
  flow : Flow Path
  throughput : ℝ
  weight : R → ℝ
  distance : D → ℝ
  flow_feasible : IsConcurrent a c flow throughput
  weight_nonneg : ∀ r, 0 ≤ weight r
  distances : IsDistance a weight distance
  distance_sum_one : ∑ d, distance d = 1
  objectives_eq : throughput = cost c weight
  flow_maximal : ∀ f t, IsAtLeastConcurrent a c f t → t ≤ throughput
  ratio_minimal : ∀ w dist, (∀ r, 0 ≤ w r) → IsDistance a w dist →
    0 < (∑ d, dist d) → cost c weight ≤ cost c w / (∑ d, dist d)

/-- Attained strong duality from only an explicit positive-normalization witness.
The witness is arbitrary and need not minimize either objective. -/
theorem exists_solution (a : ∀ d, R → Path d → ℕ) (c : R → ℝ)
    (hc : ∀ r, 0 ≤ c r) (w₀ : R → ℝ) (dist₀ : D → ℝ)
    (hw₀ : ∀ r, 0 ≤ w₀ r) (hd₀ : IsDistance a w₀ dist₀)
    (hs₀ : 0 < ∑ d, dist₀ d) : Nonempty (Solution a c) := by
  classical
  have : ∀ d, Nonempty (Path d) := fun d => ⟨(hd₀ d).2.choose⟩
  have hpos := positive_profile_of_covering (normalized_covering hw₀ hd₀ hs₀)
  obtain ⟨F, w, hF, hw, hEq, hMax, _hMin, _hw1⟩ :=
    IntegerPackingCovering.strong_duality (profileIncidence a) hc hpos
  obtain ⟨dist, hd⟩ := exists_distances a w
  have hs : 1 ≤ ∑ d, dist d := ((covering_iff_distanceSum hd).mp hw).2
  have hspos : 0 < ∑ d, dist d := lt_of_lt_of_le zero_lt_one hs
  let s : ℝ := 1 / (∑ d, dist d)
  let z : R → ℝ := fun r => s * w r
  let e : D → ℝ := fun d => s * dist d
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hz : ∀ r, 0 ≤ z r := fun r => mul_nonneg hs0 (hw.1 r)
  have he : IsDistance a z e := distance_scale hd hs0
  have he1 : ∑ d, e d = 1 := by simp [e, s, ← Finset.mul_sum, hspos.ne']
  have hzcov : IntegerPackingCovering.IsCovering (profileIncidence a) z :=
    (covering_iff_distanceSum he).mpr ⟨hz, he1.ge⟩
  have hcost : cost c z = IntegerPackingCovering.packingValue F := by
    apply le_antisymm _ (IntegerPackingCovering.weak_duality _ hF hzcov)
    rw [hEq]
    have hwcost : 0 ≤ cost c w := Finset.sum_nonneg fun r _ => mul_nonneg (hc r) (hw.1 r)
    have hs1 : s ≤ 1 := (div_le_one hspos).mpr hs
    simpa only [z, cost_scale, one_mul] using mul_le_mul_of_nonneg_right hs1 hwcost
  refine ⟨⟨marginal F, IntegerPackingCovering.packingValue F, z, e,
    marginal_isConcurrent a hF, hz, he, he1, hcost.symm, ?_, ?_⟩⟩
  · intro f t hf
    obtain ⟨g, hg⟩ := trim_atLeastConcurrent a hf
    obtain ⟨F', hF', hFt⟩ := exists_profile_packing a hc hg
    rw [← hFt]
    exact hMax F' hF'
  · intro z' e' hz' he' hS'
    have hcover := normalized_covering hz' he' hS'
    have hweak := IntegerPackingCovering.weak_duality (profileIncidence a) hF hcover
    rw [← hcost] at hweak
    change cost c z ≤ cost c (fun r => (1 / (∑ d, e' d)) * z' r) at hweak
    rw [cost_scale c z' (1 / (∑ d, e' d))] at hweak
    simpa [div_eq_mul_inv, mul_comm] using hweak

/-- A feasible normalization entails a nonempty demand family. -/
theorem demand_card_pos {a : ∀ d, R → Path d → ℕ} {c : R → ℝ} (S : Solution a c) :
    0 < Fintype.card D := by
  by_contra h
  have hz : Fintype.card D = 0 := Nat.eq_zero_of_not_pos h
  let : IsEmpty D := Fintype.card_eq_zero_iff.mp hz
  have hs := S.distance_sum_one
  simp at hs

/-- Average-distance normalization retains the division by the demand count.
Its raw mass is precisely m times the sum-one optimizer's raw mass. -/
theorem average_normalization {a : ∀ d, R → Path d → ℕ} {c : R → ℝ}
    (S : Solution a c) (hm : 0 < Fintype.card D) :
    ∃ w dist, (∀ r, 0 ≤ w r) ∧ IsDistance a w dist ∧
      (∑ d, dist d) = (Fintype.card D : ℝ) ∧
      S.throughput = cost c w / (Fintype.card D : ℝ) ∧
      (∑ r, w r) = (Fintype.card D : ℝ) * (∑ r, S.weight r) := by
  let m : ℝ := Fintype.card D
  have hmpos : 0 < m := by change 0 < (Fintype.card D : ℝ); exact_mod_cast hm
  refine ⟨fun r => m * S.weight r, fun d => m * S.distance d,
    fun r => mul_nonneg hmpos.le (S.weight_nonneg r),
    distance_scale S.distances hmpos.le, ?_, ?_, ?_⟩
  · simp [← Finset.mul_sum, S.distance_sum_one, m]
  · rw [cost_scale, S.objectives_eq]
    exact (mul_div_cancel_left₀ _ hmpos.ne').symm
  · exact (Finset.mul_sum _ _ _).symm

end
end DirectedFlowCutGap.ConcurrentDuality
