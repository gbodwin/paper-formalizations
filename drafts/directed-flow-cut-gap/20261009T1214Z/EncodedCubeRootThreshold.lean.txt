import DirectedFlowCutGap.RawNonnegativeRational

/-!
# A positive natural cube-root ceiling and rational heavy threshold

The bounded search tests `k*k*k` using two natural multiplications. Its fuel is
the graph cardinality, so even this simple linear search is polynomial in the
graph input size. Binary cost/weight values never determine the loop length.
The resulting positive integer q satisfies n≤q³ and q³≤8n for positive n;
the threshold 1/(4q) therefore needs no real-power evaluation.
-/

namespace DirectedFlowCutGap.EncodedCubeRootThreshold

open scoped NNReal
open RawNonnegativeRational

def cube (k : ℕ) : ℕ := k*k*k

def search (n : ℕ) : ℕ → ℕ → ℕ × ℕ
  | k,0 => (k,1)
  | k,fuel+1 =>
    if n ≤ cube k then (k,5) else
      let r := search n (k+1) fuel
      (r.1,r.2+7)

theorem search_lower (n k fuel : ℕ) : k ≤ (search n k fuel).1 := by
  induction fuel generalizing k with
  | zero => simp [search]
  | succ fuel ih =>
    simp only [search]
    split
    · omega
    · have h := ih (k+1)
      omega

theorem search_upper (n k fuel : ℕ) : (search n k fuel).1 ≤ k+fuel := by
  induction fuel generalizing k with
  | zero => simp [search]
  | succ fuel ih =>
    simp only [search]
    split
    · omega
    · have h := ih (k+1)
      omega

theorem search_spec (n k fuel : ℕ) (h : n ≤ cube (k+fuel)) :
    n ≤ cube (search n k fuel).1 := by
  induction fuel generalizing k with
  | zero => simpa [search] using h
  | succ fuel ih =>
    simp only [search]
    split
    · assumption
    · apply ih
      simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using h

theorem search_minimal (n k fuel : ℕ) (j : ℕ) (hk : k ≤ j)
    (hj : j < (search n k fuel).1) : cube j < n := by
  induction fuel generalizing k with
  | zero => simp only [search] at hj; omega
  | succ fuel ih =>
    by_cases h : n ≤ cube k
    · simp only [search,h,↓reduceIte] at hj
      omega
    · rcases Nat.eq_or_lt_of_le hk with rfl | hkj
      · exact lt_of_not_ge h
      · apply ih (k+1) (by omega)
        simpa only [search,h,↓reduceIte] using hj

theorem search_work (n k fuel : ℕ) : (search n k fuel).2 ≤ 7*fuel+5 := by
  induction fuel generalizing k with
  | zero => simp [search]
  | succ fuel ih =>
    simp only [search]
    split
    · omega
    · have h := ih (k+1)
      omega

def ceilCube (n : ℕ) : ℕ := (search n 1 n).1

theorem ceilCube_positive (n : ℕ) : 0 < ceilCube n := search_lower n 1 n

theorem ceilCube_upper (n : ℕ) : ceilCube n ≤ n+1 := by
  simpa only [ceilCube,Nat.add_comm] using search_upper n 1 n

theorem le_cube_ceilCube (n : ℕ) : n ≤ cube (ceilCube n) := by
  apply search_spec
  dsimp [cube]
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*n*n)]

theorem predecessor_cube_lt (n : ℕ) (hn : 0<n) : cube (ceilCube n-1)<n := by
  have hp := ceilCube_positive n
  by_cases hq : ceilCube n=1
  · simpa [hq,cube] using hn
  · exact search_minimal n 1 n (ceilCube n-1) (by omega) (by change _ < ceilCube n; omega)

/-- Pure integer certificates for the constant-factor cube-root proxy. -/
theorem cube_ceilCube_le (n : ℕ) (hn : 0<n) : cube (ceilCube n) ≤ 8*n := by
  have hp := ceilCube_positive n
  by_cases hq : ceilCube n=1
  · simp only [hq,cube]
    omega
  · have hq' : ceilCube n ≤ 2*(ceilCube n-1) := by omega
    have hb := Nat.pow_le_pow_left hq' 3
    have hm := Nat.mul_le_mul_left 8 (predecessor_cube_lt n hn).le
    dsimp [cube] at hm ⊢
    nlinarith

theorem cube_operand_bound (n k : ℕ) (hk : k≤n+1) :
    cube k ≤ 2^(3*Nat.size (n+1)) := by
  have hb : k ≤ 2^Nat.size (n+1) := hk.trans (Nat.lt_size_self _).le
  have hp := Nat.pow_le_pow_left hb 3
  calc
    cube k = k^3 := by simp [cube,pow_succ]
    _ ≤ (2^Nat.size (n+1))^3 := hp
    _ = _ := by rw [← pow_mul]; congr 1; omega

def threshold (n : ℕ) : Code :=
  let q := ceilCube n
  ⟨1,4*q,Nat.mul_pos (by decide) (ceilCube_positive n)⟩

def thresholdWithCost (n : ℕ) : Code × ℕ :=
  let r := search n 1 n
  (⟨1,4*r.1,Nat.mul_pos (by decide) (ceilCube_positive n)⟩,r.2+7)

@[simp] theorem thresholdWithCost_value (n : ℕ) : (thresholdWithCost n).1=threshold n := rfl

theorem threshold_work (n : ℕ) : (thresholdWithCost n).2 ≤ 7*n+12 := by
  have h := search_work n 1 n
  change (search n 1 n).2+7 ≤ _
  omega

@[simp] theorem threshold_value (n : ℕ) :
    (threshold n).realValue = 1/(4*(ceilCube n : ℝ≥0)) := by
  simp [threshold,Code.realValue,Code.value]

theorem threshold_positive (n : ℕ) : 0 < (threshold n).realValue := by
  rw [threshold_value]
  have h : (0 : ℝ≥0) < ceilCube n := by exact_mod_cast ceilCube_positive n
  positivity

theorem threshold_le_quarter (n : ℕ) : (threshold n).realValue ≤ 1/4 := by
  rw [threshold_value]
  have h : (1 : ℝ≥0) ≤ ceilCube n := by exact_mod_cast ceilCube_positive n
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

theorem reciprocal_threshold (n : ℕ) : 1/(threshold n).realValue = 4*(ceilCube n : ℝ≥0) := by
  simp [threshold_value]

theorem threshold_bounded (n : ℕ) :
    (threshold n).Bounded (Nat.size (4*ceilCube n)) :=
  ⟨Nat.one_le_two_pow,(Nat.lt_size_self _).le⟩

theorem threshold_bits (n : ℕ) :
    Nat.size (threshold n).num ≤ Nat.size (4*(n+1))+1 ∧
      Nat.size (threshold n).den ≤ Nat.size (4*(n+1))+1 := by
  have hb := Code.bounded_bits (threshold_bounded n)
  have hs := Nat.size_le_size (Nat.mul_le_mul_left 4 (ceilCube_upper n))
  constructor <;> omega

end DirectedFlowCutGap.EncodedCubeRootThreshold
