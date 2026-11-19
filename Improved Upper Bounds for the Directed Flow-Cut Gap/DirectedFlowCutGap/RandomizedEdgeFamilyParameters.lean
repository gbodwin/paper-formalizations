import DirectedFlowCutGap.RandomizedEdgeFamily
import DirectedFlowCutGap.EncodedDyadicRoot

/-!
# Computable factors for the adaptive edge family

For each positive exponent the analysis supplies two fixed natural constants.
After those constants are fixed, the graph-dependent factor is computed from
the original rational weights using ceilings, bit lengths and powers of two.
The computation does not evaluate the real expectation or a real power.
-/

namespace DirectedFlowCutGap.RandomizedEdgeFamily

open scoped NNRat NNReal ENNReal BigOperators
open RationalEdgeDecomposition

private def root {k : ℕ} (r : ℕ) : ℕ :=
  (EncodedDyadicRoot.powerTwo ((r.size + k - 1) / k)).1

private theorem root_positive (r k : ℕ) : 0 < root (k := k) r := by
  rw [root, EncodedDyadicRoot.powerTwo_value]
  positivity

private theorem root_bounds {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    (r : ℝ) ^ (k : ℝ)⁻¹ ≤ root (k := k) r ∧
      (root (k := k) r : ℝ) ≤ 2 * (r : ℝ) ^ (k : ℝ)⁻¹ := by
  let e := (r.size + k - 1) / k
  have he : r.size ≤ k * e :=
    (ceilDiv_le_iff_le_mul hk).mp (le_refl (r.size ⌈/⌉ k))
  have ha : k * e ≤ r.size + k - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have hs := Nat.size_pos.mpr hr
  have hl : r ≤ (2 ^ e) ^ k := by
    rw [← pow_mul, Nat.mul_comm e k]
    exact r.lt_size_self.le.trans (Nat.pow_le_pow_right (by decide) he)
  have hu : (2 ^ e) ^ k ≤ 2 ^ k * r := by
    rw [← pow_mul, Nat.mul_comm e k]
    calc
      _ ≤ 2 ^ (k + (r.size - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ k * 2 ^ (r.size - 1) := pow_add ..
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.lt_size.mp (by omega))
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlR : (r : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hl
  have huR : ((2 ^ e : ℕ) : ℝ) ^ (k : ℝ) ≤
      (2 * (r : ℝ) ^ (k : ℝ)⁻¹) ^ (k : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast, mul_pow,
      Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) hk.ne']
    exact_mod_cast hu
  rw [root, EncodedDyadicRoot.powerTwo_value]
  exact ⟨(Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) hkR).mpr hlR,
    (Real.rpow_le_rpow_iff (by positivity) (by positivity) hkR).mp huR⟩

def massCeiling {n : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : ℕ :=
  max 1 ⌈2 * originalTotal adj w⌉₊

def parameters {n : ℕ} (exponentDenominator multiplier confidence : ℕ)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n) : Input n :=
  ⟨adj, w, ((multiplier * root (k := exponentDenominator) (max 1 n) *
    root (k := 2) (massCeiling adj w) : ℕ) : ℚ≥0), confidence,.mass⟩

private theorem mass_le {n : ℕ} (D : Input n) (c : Edge n → ℚ≥0) :
    (totalEdgeWeight (request D c).graph (fun e => (adjusted D e : ℝ≥0)) : ℝ) ≤
      2 * (originalTotal D.adjacency D.weights : ℝ) := by
  classical
  have hsum : (∑ e, adjusted D e) ≤ 2 * originalTotal D.adjacency D.weights := by
    rw [originalTotal, Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => modified_le D.adjacency D.weights e
  simp only [totalEdgeWeight, NNReal.coe_sum]
  calc
    _ ≤ ∑ e, (adjusted D e : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => NNRat.cast_nonneg _)
    _ ≤ _ := by
      simpa only [NNRat.cast_sum, NNRat.cast_mul, NNRat.cast_ofNat] using (NNRat.cast_le (K := ℝ)).mpr hsum

private theorem mass_ceil_bounds {n : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) :
    2 * (originalTotal adj w : ℝ) ≤ (massCeiling adj w : ℝ) ∧
      (massCeiling adj w : ℝ) ≤ 2 * (originalTotal adj w : ℝ) + 1 := by
  let W := originalTotal adj w
  have hlo := (NNRat.cast_le (K := ℝ)).mpr (Nat.le_ceil (2 * W))
  have hhi := (NNRat.cast_lt (K := ℝ)).mpr (Nat.ceil_lt_add_one (show 0 ≤ 2 * W by positivity))
  simp only [massCeiling, Nat.cast_max, Nat.cast_one]
  push_cast at hlo hhi
  exact ⟨hlo.trans (le_max_right _ _), max_le (le_add_of_nonneg_left (by positivity)) hhi.le⟩

theorem parameters_factor_ge_one {n k M κ : ℕ} (hM : 0 < M)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n) :
    1 ≤ (parameters k M κ adj w).factor := by
  have ha : 0 < M * root (k := k) (max 1 n) * root (k := 2) (massCeiling adj w) :=
    Nat.mul_pos (Nat.mul_pos hM (root_positive ..)) (root_positive ..)
  change (1 : ℚ≥0) ≤ ((M * root (k := k) (max 1 n) * root (k := 2) (massCeiling adj w) : ℕ) : ℚ≥0)
  exact_mod_cast Nat.succ_le_of_lt ha

private theorem factor_value {n k M κ : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) :
    ((parameters k M κ adj w).factor : ℝ) =
      (M : ℝ) * (root (k := k) (max 1 n) : ℝ) * (root (k := 2) (massCeiling adj w) : ℝ) := by
  change (((M * root (k := k) (max 1 n) * root (k := 2) (massCeiling adj w) : ℕ) : ℚ≥0) : ℝ) = _
  rw [NNRat.cast_natCast, Nat.cast_mul, Nat.cast_mul]

theorem parameters_expected_bound {n k M κ : ℕ} (hn : 0 < n) (hk : 0 < k)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (K : ℝ) (hM : 2 * K ≤ M)
    (hbound : ∀ c : Edge n → ℚ≥0,
      let D := parameters k M κ adj w
      let I := request D c
      EncodedEdgeSolver.expectedPrice I EncodedEdgeSolver.massMode ≤
        K * (n : ℝ) ^ (k : ℝ)⁻¹ *
          (totalEdgeWeight I.graph (fun e => (adjusted D e : ℝ≥0)) : ℝ) ^ (1 / 2 : ℝ) *
          (weightedEdgeCost I.graph I.cost (fun e => (adjusted D e : ℝ≥0)) : ℝ)) :
    expectedPriceBound (parameters k M κ adj w) := by
  intro c
  let D := parameters k M κ adj w
  let I := request D c
  let W := (totalEdgeWeight I.graph (fun e => (adjusted D e : ℝ≥0)) : ℝ)
  have hn' : max 1 n = n := max_eq_right hn
  have hroot := (root_bounds (r := n) hn hk).1
  have hceil := (root_bounds (r := massCeiling adj w) (by
    exact (Nat.zero_lt_succ 0).trans_le (le_max_left _ _)) (k := 2) (by decide)).1
  have hW : W ≤ (massCeiling adj w : ℝ) := (mass_le D c).trans (mass_ceil_bounds adj w).1
  have hw := (Real.rpow_le_rpow (by positivity : 0 ≤ W) hW (by norm_num : 0 ≤ (1 / 2 : ℝ))).trans
    (by simpa only [Nat.cast_ofNat, one_div] using hceil)
  have hα : K * (n : ℝ) ^ (k : ℝ)⁻¹ * W ^ (1 / 2 : ℝ) ≤ (D.factor : ℝ) / 2 := by
    change _ ≤ ((parameters k M κ adj w).factor : ℝ) / 2
    rw [factor_value, hn', le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc
      _ = (2 * K) * (n : ℝ) ^ (k : ℝ)⁻¹ * W ^ (1 / 2 : ℝ) := by ring
      _ ≤ _ := by gcongr
  have hb := hbound c
  apply hb.trans
  rw [weighted_cost]
  refine (mul_le_mul_of_nonneg_right hα (by positivity)).trans_eq ?_
  change (D.factor : ℝ) / 2 * (∑ e, (c e : ℝ) * (adjusted D e : ℝ)) = (allowance D c : ℝ)
  simp only [allowance, NNRat.cast_div, NNRat.cast_mul, NNRat.cast_sum, NNRat.cast_ofNat]
  ring

theorem parameters_factor_le {n k M κ : ℕ} (hn : 0 < n) (hk : 0 < k)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (hW : 1 ≤ originalTotal adj w) :
    ((parameters k M κ adj w).factor : ℝ) ≤
      8 * (M : ℝ) * (n : ℝ) ^ (k : ℝ)⁻¹ * (originalTotal adj w : ℝ) ^ (1 / 2 : ℝ) := by
  let W := (originalTotal adj w : ℝ)
  have hW' : 1 ≤ W := by simpa only [NNRat.cast_one] using (NNRat.cast_le (K := ℝ)).mpr hW
  have hmass : (massCeiling adj w : ℝ) ≤ 4 * W := (mass_ceil_bounds adj w).2.trans (by linarith)
  have hroot := (root_bounds (r := n) hn hk).2
  have hceil := (root_bounds (r := massCeiling adj w) (by
    exact (Nat.zero_lt_succ 0).trans_le (le_max_left _ _)) (k := 2) (by decide)).2
  have hWroot : (massCeiling adj w : ℝ) ^ (1 / 2 : ℝ) ≤ 2 * W ^ (1 / 2 : ℝ) := by
    refine (Real.rpow_le_rpow (by positivity) hmass (by norm_num)).trans_eq ?_
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.sqrt_eq_rpow]
    norm_num
  have hroot' : (root (k := 2) (massCeiling adj w) : ℝ) ≤ 4 * W ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ 2 * (massCeiling adj w : ℝ) ^ (1 / 2 : ℝ) := by simpa only [Nat.cast_ofNat, one_div] using hceil
      _ ≤ 2 * (2 * W ^ (1 / 2 : ℝ)) := by gcongr
      _ = _ := by ring
  rw [factor_value, max_eq_right hn]
  calc
    _ ≤ (M : ℝ) * (2 * (n : ℝ) ^ (k : ℝ)⁻¹) * (4 * W ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by dsimp only [W]; ring

theorem computable_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ k M : ℕ, 0 < k ∧ 0 < M ∧
      ∀ (n : ℕ) (_ : 0 < n) (adj : BinaryFractionalWalkOracle.Adjacency n)
        (w : RationalEdgeThresholds.Weights n) (κ : ℕ),
        let D := parameters k M κ adj w
        1 ≤ D.factor ∧ expectedPriceBound D ∧
          (1 ≤ originalTotal adj w →
            (D.factor : ℝ) ≤ 8 * (M : ℝ) * (n : ℝ) ^ ε *
              (originalTotal adj w : ℝ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  let k := j + 1
  have hk : 0 < k := Nat.succ_pos _
  have hkR : 0 < (k : ℝ)⁻¹ := by positivity
  have hke : (k : ℝ)⁻¹ ≤ ε := by
    simpa only [k, Nat.cast_add, Nat.cast_one, one_div] using hj.le
  obtain ⟨K, hK, bound⟩ := EncodedEdgeSolver.mass_expected_uniform (k : ℝ)⁻¹ hkR
  let M := ⌈2 * K⌉₊ + 1
  have hM : 0 < M := Nat.succ_pos _
  have hKM : 2 * K ≤ (M : ℝ) := (Nat.le_ceil _).trans (by unfold M; push_cast; linarith)
  refine ⟨k, M, hk, hM, ?_⟩
  intro n hn adj w κ
  refine ⟨parameters_factor_ge_one hM _ _, parameters_expected_bound hn hk adj w K hKM ?_, ?_⟩
  · intro c
    exact bound n _ _ (modified_feasible adj w)
  · intro hW
    apply (parameters_factor_le hn hk adj w hW).trans
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast hn) hke
    gcongr

/-- The size calibration uses the same price multiplier and a cubic-root
factor in the original vertex count. -/
def sizeParameters {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : Input n :=
  ⟨adj,w,((M*root (k:=k) (max 1 n)*root (k:=3) (max 1 n) : ℕ) : ℚ≥0),κ,.size⟩

private theorem size_factor {n k M κ : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) :
    ((sizeParameters k M κ adj w).factor:ℝ) =
      (M:ℝ)*(root (k:=k) (max 1 n):ℝ)*(root (k:=3) (max 1 n):ℝ) := by
  change (((M*root (k:=k) (max 1 n)*root (k:=3) (max 1 n) : ℕ) : ℚ≥0) : ℝ) = _
  rw [NNRat.cast_natCast,Nat.cast_mul,Nat.cast_mul]

private theorem size_factor_ge_one {n k M κ : ℕ} (hM : 0<M) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : 1 ≤ (sizeParameters k M κ adj w).factor := by
  have positive := Nat.mul_pos (Nat.mul_pos hM (root_positive (max 1 n) k)) (root_positive (max 1 n) 3)
  change (1 : ℚ≥0) ≤ ((M*root (k:=k) (max 1 n)*root (k:=3) (max 1 n) : ℕ) : ℚ≥0)
  exact_mod_cast Nat.succ_le_of_lt positive

def preferMass {n : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : Prop :=
  root (k:=2) (massCeiling adj w) ≤ root (k:=3) (max 1 n)

instance preferMassDecidable {n : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : Decidable (preferMass adj w) :=
  by
  unfold preferMass
  infer_instance

def bestParameters {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : Input n :=
  let chosen := if preferMass adj w then (root (k:=2) (massCeiling adj w),CheckedEdgeOracle.Strategy.mass)
    else (root (k:=3) (max 1 n),CheckedEdgeOracle.Strategy.size)
  ⟨adj,w,((M*root (k:=k) (max 1 n)*chosen.1 : ℕ) : ℚ≥0),κ,chosen.2⟩

theorem bestParameters_mass {n k M κ : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (h : preferMass adj w) :
    bestParameters k M κ adj w=parameters k M κ adj w := by
  simp only [bestParameters,h,ite_true,parameters]

theorem bestParameters_size {n k M κ : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (h : ¬preferMass adj w) :
    bestParameters k M κ adj w=sizeParameters k M κ adj w := by
  simp only [bestParameters,h,ite_false,sizeParameters]

theorem best_factor_nat {n k M κ : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) :
    (bestParameters k M κ adj w).factor =
      ((M*root (k:=k) (max 1 n)*min (root (k:=2) (massCeiling adj w)) (root (k:=3) (max 1 n)) : ℕ) : ℚ≥0) := by
  by_cases h : preferMass adj w
  · rw [bestParameters_mass adj w h]
    change root (k:=2) (massCeiling adj w) ≤ root (k:=3) (max 1 n) at h
    rw [min_eq_left h]
    rfl
  · rw [bestParameters_size adj w h]
    change ¬root (k:=2) (massCeiling adj w) ≤ root (k:=3) (max 1 n) at h
    rw [min_eq_right (le_of_not_ge h)]
    rfl

theorem best_factor_bounds {n k M κ : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) :
    (bestParameters k M κ adj w).factor ≤ (parameters k M κ adj w).factor ∧
      (bestParameters k M κ adj w).factor ≤ (sizeParameters k M κ adj w).factor := by
  rw [best_factor_nat]
  let a := M*root (k:=k) (max 1 n)
  let b := root (k:=2) (massCeiling adj w)
  let c := root (k:=3) (max 1 n)
  have bound (r : ℕ) (h : min b c ≤ r) : ((a*min b c : ℕ) : ℚ≥0) ≤ ((a*r : ℕ) : ℚ≥0) := by
    exact_mod_cast Nat.mul_le_mul_left a h
  exact ⟨bound b (min_le_left ..),bound c (min_le_right ..)⟩

theorem best_factor_ge_one {n k M κ : ℕ} (hM : 0<M) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : 1 ≤ (bestParameters k M κ adj w).factor := by
  by_cases h : preferMass adj w
  · rw [bestParameters_mass adj w h]
    exact parameters_factor_ge_one hM adj w
  · rw [bestParameters_size adj w h]
    exact size_factor_ge_one hM adj w

private theorem size_expected {n k M κ : ℕ} (hn : 0<n) (hk : 0<k) (K : ℝ) (_hK : 0<K)
    (hM : 2*K≤M) (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (bound : ∀ c : Edge n → ℚ≥0,
      let D := sizeParameters k M κ adj w
      let I := request D c
      EncodedEdgeSolver.expectedPrice I EncodedEdgeSolver.sizeMode ≤
        K*(n:ℝ)^(1/3+(k:ℝ)⁻¹)*(weightedEdgeCost I.graph I.cost (fun e => (adjusted D e:ℝ≥0)):ℝ)) :
    expectedPriceBound (sizeParameters k M κ adj w) := by
  let D := sizeParameters k M κ adj w
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have roots := (root_bounds (r:=n) (k:=k) hn hk).1
  have cubic := (root_bounds (r:=n) (k:=3) hn (by decide)).1
  norm_num only [Nat.cast_ofNat] at cubic
  have cast (κ : ℕ) : ((sizeParameters k M κ adj w).factor:ℝ) =
      (M:ℝ)*(root (k:=k) n:ℝ)*(root (k:=3) n:ℝ) := by
    rw [size_factor,max_eq_right hn]
  have cap : K*(n:ℝ)^(1/3+(k:ℝ)⁻¹) ≤ (D.factor:ℝ)/2 := by
    rw [cast,Real.rpow_add hnR,one_div]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have h : (2*K)*(n:ℝ)^(k:ℝ)⁻¹*(n:ℝ)^(3:ℝ)⁻¹ ≤
        (M:ℝ)*(root (k:=k) n:ℝ)*(root (k:=3) n:ℝ) := by
      gcongr
      simpa only [one_div] using cubic
    calc
      _ = (2*K)*(n:ℝ)^(k:ℝ)⁻¹*(n:ℝ)^(3:ℝ)⁻¹ := by ring
      _ ≤ _ := h
  intro c
  have est := bound c
  change EncodedEdgeSolver.expectedPrice (request D c) EncodedEdgeSolver.sizeMode ≤
    K*(n:ℝ)^(1/3+(k:ℝ)⁻¹)*(weightedEdgeCost (request D c).graph (request D c).cost
      (fun e => (adjusted D e:ℝ≥0)):ℝ) at est
  rw [weighted_cost] at est
  refine est.trans ((mul_le_mul_of_nonneg_right cap (by positivity)).trans_eq ?_)
  change (D.factor:ℝ)/2 * (∑ e, (c e:ℝ)*(adjusted D e:ℝ)) = (allowance D c:ℝ)
  simp only [allowance,NNRat.cast_div,NNRat.cast_mul,NNRat.cast_sum,NNRat.cast_ofNat]
  ring

private theorem size_factor_le {n k M κ : ℕ} (hn : 0<n) (hk : 0<k)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n) :
    ((sizeParameters k M κ adj w).factor:ℝ) ≤ 4*(M:ℝ)*(n:ℝ)^((k:ℝ)⁻¹+1/3) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have rk := (root_bounds (r:=n) (k:=k) hn hk).2
  have rs := (root_bounds (r:=n) (k:=3) hn (by decide)).2
  norm_num only [Nat.cast_ofNat] at rs
  rw [size_factor,max_eq_right hn,Real.rpow_add hnR,one_div]
  calc
    _ ≤ (M:ℝ)*(2*(n:ℝ)^(k:ℝ)⁻¹)*(2*(n:ℝ)^(3:ℝ)⁻¹) := by
      gcongr
      simpa only [one_div] using rs
    _ = _ := by ring

theorem computable_best_parameters (ε : ℝ) (hε : 0<ε) :
    ∃ k M : ℕ, 0<k ∧ 0<M ∧
      ∀ (n : ℕ), 0<n → ∀ (adj : BinaryFractionalWalkOracle.Adjacency n)
        (w : RationalEdgeThresholds.Weights n) (κ : ℕ),
        let D := bestParameters k M κ adj w
        1≤D.factor ∧ expectedPriceBound D ∧
          (1≤originalTotal adj w →
            (D.factor:ℝ) ≤ min
              (8*(M:ℝ)*(n:ℝ)^ε*(originalTotal adj w:ℝ)^(1/2:ℝ))
              (8*(M:ℝ)*(n:ℝ)^(ε+1/3))) := by
  obtain ⟨j,hj⟩ := exists_nat_one_div_lt hε
  let k := j+1
  have hk : 0<k := Nat.succ_pos _
  have hkR : 0<(k:ℝ)⁻¹ := by positivity
  have hke : (k:ℝ)⁻¹ ≤ ε := by
    simpa only [k,Nat.cast_add,Nat.cast_one,one_div] using hj.le
  obtain ⟨A,hA,ma⟩ := EncodedEdgeSolver.mass_expected_uniform (k:ℝ)⁻¹ hkR
  obtain ⟨B,hB,si⟩ := EncodedEdgeSolver.size_expected_uniform (k:ℝ)⁻¹ hkR
  let M := ⌈2*(A+B)⌉₊+1
  have hM : 0<M := Nat.succ_pos _
  have bounds : 2*(A+B) ≤ (M:ℝ) := (Nat.le_ceil _).trans (by unfold M; push_cast; linarith)
  refine ⟨k,M,hk,hM,fun n hn adj w κ => ?_⟩
  have loose : (1:ℝ)≤n := by exact_mod_cast hn
  have mass : expectedPriceBound (parameters k M κ adj w) :=
    parameters_expected_bound hn hk adj w A (by linarith) (fun c => ma n _ _ (modified_feasible adj w))
  have size : expectedPriceBound (sizeParameters k M κ adj w) :=
    size_expected hn hk B hB (by linarith) adj w (fun c => si n _ _ (modified_feasible adj w))
  have valid : expectedPriceBound (bestParameters k M κ adj w) := by
    by_cases h : preferMass adj w
    · rw [bestParameters_mass adj w h]
      exact mass
    · rw [bestParameters_size adj w h]
      exact size
  refine ⟨best_factor_ge_one hM adj w,valid,fun hW => ?_⟩
  have limiting := best_factor_bounds (k:=k) (M:=M) (κ:=κ) adj w
  apply le_min
  · apply ((NNRat.cast_le (K:=ℝ)).mpr limiting.1).trans
    apply (parameters_factor_le hn hk adj w hW).trans
    have powers := Real.rpow_le_rpow_of_exponent_le loose hke
    gcongr
  · apply ((NNRat.cast_le (K:=ℝ)).mpr limiting.2).trans
    apply (size_factor_le hn hk adj w).trans
    have powers := Real.rpow_le_rpow_of_exponent_le loose (add_le_add hke (le_refl (1/3:ℝ)))
    gcongr
    norm_num

open FiniteDrawTrees
open RationalWeakFamily (History)
open CheckedMWHistory (occurrences)

private theorem empty_good {n : ℕ} (D : Input n) (h : originalTotal D.adjacency D.weights < 1) :
    Good D.adjacency D.weights ∅ := by
  let G := BinaryFractionalWalkOracle.graph D.adjacency
  let w := RationalEdgeThresholds.weights D.weights
  have hW : totalEdgeWeight G w = (originalTotal D.adjacency D.weights : ℝ≥0) := by
    classical
    simp only [totalEdgeWeight, graphEdges, Finset.sum_filter, originalTotal, NNRat.cast_sum,
      originalWeight_eq, actualEdgeWeight, G, w]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : (BinaryFractionalWalkOracle.graph D.adjacency).Adj e.1 e.2
    · simp only [ite_eq_left he]
    · simp only [ite_eq_right he]
  have hsmall : totalEdgeWeight G w < 1 := by
    rw [hW, ← NNRat.cast_one (α := ℝ≥0)]
    exact (NNRat.cast_lt (K := ℝ≥0)).mpr h
  refine ⟨Finset.empty_subset _, ?_⟩
  intro s t hst path
  have ht : 1 ≤ edgeDistance G w s t :=
    (RationalEdgeThresholds.demands_iff D.adjacency D.weights (s, t)).mp hst
  have hpath := (coe_le_edgeDistance_iff G w s t 1).mp (by simpa only [ENNReal.coe_one] using ht) path
  have hle : path.edgeWeight w ≤ totalEdgeWeight G w :=
    Finset.sum_le_sum_of_subset path.edges_subset_graphEdges
  exact False.elim (not_lt_of_ge (hpath.trans hle) hsmall)

private def emptyHistory {n : ℕ} (D : Input n) : History (Edge n) :=
  ⟨fun _ => 1, List.replicate (rounds D) ∅⟩

/-- If the total original mass is below one, all threshold demands are
unreachable and the full family of empty cuts requires no random bits. -/
def familyTree {n : ℕ} (D : Input n) : FiniteDrawTrees.Tree (Option (History (Edge n))) :=
  if originalTotal D.adjacency D.weights < 1 then .pure (some (emptyHistory D)) else build D

theorem familyTree_within {n B : ℕ} (hn : 0 < n) (D : Input n) (hα : 1 ≤ D.factor) (h : InputFits D B) :
    Within (readBudget n B D.confidence) (familyTree D) := by
  unfold familyTree
  split
  · exact .pure _ _
  · exact within_build hn D hα h

theorem familyTree_binary {n : ℕ} (D : Input n) : LazyFairBitTrees.Binary (familyTree D) := by
  unfold familyTree
  split
  · exact .pure _
  · exact build_binary D

theorem familyTree_failure {n B : ℕ} (hn : 0 < n) (D : Input n) (hα : 1 ≤ D.factor)
    (h : InputFits D B) (hMean : expectedPriceBound D) :
    ((EncodedSolverBits.fairTape (readBudget n B D.confidence)).map
      (fun tape => ((EncodedSolverBits.run (familyTree D) tape).map Prod.fst).join)) none ≤
      (rounds D : ℝ≥0∞) * ENNReal.ofReal (((max 1 n : ℕ) : ℝ) ^ (-(D.confidence : ℝ))) := by
  by_cases hs : originalTotal D.adjacency D.weights < 1
  · simp [familyTree, hs, EncodedSolverBits.run, FiniteDrawTrees.execute]
  · simpa only [familyTree, ite_eq_right hs] using tape_failure hn D hα h hMean

theorem familyTree_spec {n : ℕ} (hn : 0 < n) (D : Input n) (hα : 1 ≤ D.factor)
    (a : ℝ) (ha : 0 ≤ a) (hbound : 1 ≤ originalTotal D.adjacency D.weights → (D.factor : ℝ) ≤ a)
    (s : History (Edge n)) (hs : some s ∈ (ideal (familyTree D)).support) :
    s.cuts.length = rounds D ∧
      (∀ X ∈ s.cuts, Good D.adjacency D.weights X ∧ ∀ e ∈ X, 0 < adjusted D e) ∧
      ∀ e, (occurrences s e : ℝ) / (s.cuts.length : ℝ) ≤
        8 * (originalWeight D.adjacency D.weights e : ℝ) * a := by
  unfold familyTree at hs
  split_ifs at hs with hsmall
  · have he : s = emptyHistory D := by simpa [ideal, law] using hs
    subst s
    refine ⟨List.length_replicate, ?_, ?_⟩
    · intro X hx
      have hX : X = ∅ := List.eq_of_mem_replicate hx
      subst X
      exact ⟨empty_good D hsmall, by simp⟩
    · intro e
      simp only [occurrences, emptyHistory, Finset.notMem_empty, decide_false, List.countP_replicate,
        Bool.false_eq_true, ite_false, Nat.cast_zero, zero_div]
      positivity
  · obtain ⟨hlen, hvalid, hm⟩ := successful_family hn D hα s hs
    refine ⟨hlen, hvalid, fun e => (hm e).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (hbound (le_of_not_gt hsmall)) (by positivity)

private def fieldWidth {n : ℕ} (D : Input n) (e : Edge n) : ℕ :=
  let q := D.weights[e.1.val][e.2.val]
  max q.num.length q.den.length

def inputWidth {n : ℕ} (D : Input n) : ℕ :=
  max (max D.factor.num.size D.factor.den.size) (Finset.univ.sup (fieldWidth D))

theorem input_fits {n : ℕ} (D : Input n) : InputFits D (inputWidth D) := by
  have hn : D.factor.num.size ≤ inputWidth D := (le_max_left _ _).trans (le_max_left _ _)
  have hd : D.factor.den.size ≤ inputWidth D := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hn)).le
  · exact ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hd)).le
  · intro s t
    have h : fieldWidth D (s, t) ≤ inputWidth D :=
      (Finset.le_sup (f := fieldWidth D) (Finset.mem_univ (s, t))).trans (le_max_right _ _)
    exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

def calibratedParameters {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) : Input n :=
  bestParameters k M (κ + (RationalWeakFamily.edgeRounds n (originalTotal adj w)).size) adj w

@[simp] theorem calibrated_confidence_value {n : ℕ} (k M κ : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) :
    (calibratedParameters k M κ adj w).confidence =
      κ+(RationalWeakFamily.edgeRounds n (originalTotal adj w)).size := rfl

theorem calibrated_factor_ge_one {n k M κ : ℕ} (hM : 0<M)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n) :
    1≤(calibratedParameters k M κ adj w).factor :=
  best_factor_ge_one hM adj w

private theorem failure_scale {n T κ : ℕ} (hn : 2 ≤ n) :
    (T : ℝ≥0∞) * ENNReal.ofReal (((max 1 n : ℕ) : ℝ) ^ (-((κ + T.size : ℕ) : ℝ))) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-(κ : ℝ))) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpowₙ : T ≤ n ^ T.size :=
    (Nat.lt_size_self T).le.trans (Nat.pow_le_pow_left hn _)
  have hpow : (T : ℝ) ≤ (n : ℝ) ^ T.size := by exact_mod_cast hpowₙ
  have ht : (T : ℝ) * ((n : ℝ) ^ T.size)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), one_mul]
    exact hpow
  rw [max_eq_right (by omega : 1 ≤ n), ← ENNReal.ofReal_natCast T, ← ENNReal.ofReal_mul (Nat.cast_nonneg T)]
  apply ENNReal.ofReal_le_ofReal
  rw [Nat.cast_add, neg_add, Real.rpow_add hn0]
  have hs : (n : ℝ) ^ (-(T.size : ℝ)) = ((n : ℝ) ^ T.size)⁻¹ := by
    rw [Real.rpow_neg hn0.le, Real.rpow_natCast]
  rw [hs]
  calc
    _ = ((T : ℝ) * ((n : ℝ) ^ T.size)⁻¹) * (n : ℝ) ^ (-(κ : ℝ)) := by ring
    _ ≤ 1 * (n : ℝ) ^ (-(κ : ℝ)) := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = _ := one_mul _

set_option maxHeartbeats 1800000 in
/-- Run the finite adaptive family from original rational edge weights.
The theorem supplies fixed integer parameters for each positive exponent.
Every execution with enough bits preserves its unused suffix, and every
returned family has the all-demand and pointwise marginal guarantees. -/
theorem calibrated_best_families (ε : ℝ) (hε : 0 < ε) :
    ∃ k M : ℕ, 0 < k ∧ 0 < M ∧
      ∀ (n : ℕ) (_ : 2 ≤ n) (adj : BinaryFractionalWalkOracle.Adjacency n)
        (w : RationalEdgeThresholds.Weights n) (κ : ℕ),
        let D := calibratedParameters k M κ adj w
        let budget := readBudget n (inputWidth D) D.confidence
        ((EncodedSolverBits.fairTape budget).map
          (fun tape => ((EncodedSolverBits.run (familyTree D) tape).map Prod.fst).join)) none ≤
          ENNReal.ofReal ((n : ℝ) ^ (-(κ : ℝ))) ∧
        ∀ (tape : List Bool), budget ≤ tape.length →
          ∃ result used, EncodedSolverBits.run (familyTree D) tape = some (result, (tape.drop used, used)) ∧
            used ≤ budget ∧ ∀ s, result = some s →
              s.cuts.length = rounds D ∧ (∀ X ∈ s.cuts, Good adj w X) ∧
              ∀ e, (occurrences s e : ℝ) / (s.cuts.length : ℝ) ≤
                8 * (originalWeight adj w e : ℝ) *
                  min (8*(M:ℝ)*(n:ℝ)^ε*(originalTotal adj w:ℝ)^(1/2:ℝ))
                    (8*(M:ℝ)*(n:ℝ)^(ε+1/3)) := by
  obtain ⟨k, M, hk, hM, hparam⟩ := computable_best_parameters ε hε
  refine ⟨k, M, hk, hM, ?_⟩
  intro n hn adj w κ
  let D := calibratedParameters k M κ adj w
  have hn0 : 0 < n := by omega
  have prm : bestParameters k M D.confidence adj w=D := by
    rw [calibrated_confidence_value]
    rfl
  obtain ⟨hα, hMean, hf⟩ := hparam n hn0 adj w D.confidence
  rw [prm] at hα hMean hf
  have h := input_fits D
  have scale : (rounds D : ℝ≥0∞) *
      ENNReal.ofReal (((max 1 n : ℕ) : ℝ)^(-(D.confidence:ℝ))) ≤
      ENNReal.ofReal ((n:ℝ)^(-(κ:ℝ))) := by
    have confidence : D.confidence=κ+(rounds D).size := calibrated_confidence_value k M κ adj w
    rw [confidence]
    exact failure_scale hn
  refine ⟨(familyTree_failure hn0 D hα h hMean).trans scale, ?_⟩
  intro tape ht
  have hb := familyTree_binary D
  obtain ⟨result, used, hr, hu⟩ := EncodedSolverBits.complete (familyTree_within hn0 D hα h) hb tape ht
  refine ⟨result, used, hr, hu, ?_⟩
  intro s hs
  have hsupport : some s ∈ (ideal (familyTree D)).support := hs ▸ EncodedSolverBits.run_support hb hr
  obtain ⟨hlen, hvalid, hm⟩ := familyTree_spec hn0 D hα _ (by positivity) hf s hsupport
  exact ⟨hlen, fun X hx => (hvalid X hx).1, hm⟩

set_option maxHeartbeats 1800000 in
theorem calibrated_families (ε : ℝ) (hε : 0 < ε) :
    ∃ k M : ℕ, 0 < k ∧ 0 < M ∧
      ∀ (n : ℕ) (_ : 2 ≤ n) (adj : BinaryFractionalWalkOracle.Adjacency n)
        (w : RationalEdgeThresholds.Weights n) (κ : ℕ),
        let D := calibratedParameters k M κ adj w
        let budget := readBudget n (inputWidth D) D.confidence
        ((EncodedSolverBits.fairTape budget).map
          (fun tape => ((EncodedSolverBits.run (familyTree D) tape).map Prod.fst).join)) none ≤
          ENNReal.ofReal ((n : ℝ) ^ (-(κ : ℝ))) ∧
        ∀ (tape : List Bool), budget ≤ tape.length →
          ∃ result used, EncodedSolverBits.run (familyTree D) tape = some (result, (tape.drop used, used)) ∧
            used ≤ budget ∧ ∀ s, result = some s →
              s.cuts.length = rounds D ∧ (∀ X ∈ s.cuts, Good adj w X) ∧
              ∀ e, (occurrences s e : ℝ) / (s.cuts.length : ℝ) ≤
                8 * (originalWeight adj w e : ℝ) *
                  (8 * (M : ℝ) * (n : ℝ) ^ ε * (originalTotal adj w : ℝ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨k,M,hk,hM,h⟩ := calibrated_best_families ε hε
  refine ⟨k,M,hk,hM,?_⟩
  intro n hn adj w κ
  obtain ⟨chance,run⟩ := h n hn adj w κ
  refine ⟨chance,?_⟩
  intro tape enough
  obtain ⟨out,used,exactRun,reads,good⟩ := run tape enough
  refine ⟨out,used,exactRun,reads,?_⟩
  intro s hs
  obtain ⟨size,valid,freq⟩ := good s hs
  exact ⟨size,valid,fun e => (freq e).trans (mul_le_mul_of_nonneg_left (min_le_left ..) (by positivity))⟩

end DirectedFlowCutGap.RandomizedEdgeFamily
