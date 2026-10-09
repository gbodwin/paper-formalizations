import DirectedFlowCutGap.CandidateOptimization

/-!
# Finite mass accounting for analysis epochs

Mass is the actual sum of remaining frozen weights outside the current cut.
Monotonicity and geometric-decrease bounds below do not assume that current
mass equals mass at epoch start. They are accounting lemmas; the complete
random algorithm and its stopping-time probability law remain separate.
-/

namespace DirectedFlowCutGap.EpochAccounting
noncomputable section
open scoped BigOperators NNReal
open CandidateOptimization
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sum over actual remaining demand labels, preserving label multiplicity. -/
def familyMass (P : Finset (V × V)) (X : Finset V)
    (w : (V × V) → V → ℝ≥0) : ℝ≥0 :=
  ∑ p ∈ P, outsideMass X (w p)

theorem outsideMass_antitone {X Y : Finset V} (hXY : X ⊆ Y) (w : V → ℝ≥0) :
    outsideMass Y w ≤ outsideMass X w := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    obtain ⟨_, hvY⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hvX => hvY (hXY hvX)⟩
  · intros
    exact zero_le

theorem familyMass_mono {P Q : Finset (V × V)} {X Y : Finset V}
    (hQP : Q ⊆ P) (hXY : X ⊆ Y) (w : (V × V) → V → ℝ≥0) :
    familyMass Q Y w ≤ familyMass P X w := by
  calc
    _ ≤ familyMass Q X w := Finset.sum_le_sum (fun p _ => outsideMass_antitone hXY (w p))
    _ ≤ familyMass P X w := Finset.sum_le_sum_of_subset_of_nonneg hQP (by intros; exact zero_le)

@[simp] theorem familyMass_empty (X : Finset V) (w : (V × V) → V → ℝ≥0) :
    familyMass ∅ X w = 0 := by simp [familyMass]

theorem familyMass_uniform (P : Finset (V × V)) (a : ℝ≥0) :
    familyMass P ∅ (fun _ _ => a) = (P.card : ℝ≥0) * (Fintype.card V : ℝ≥0) * a := by
  simp [familyMass, outsideMass, mul_assoc]

/-- Every restart or analysis split shrinks remaining mass by the same factor. -/
theorem geometric_mass_bound (M : ℕ → ℝ≥0) (r : ℝ≥0) (k : ℕ)
    (hstep : ∀ i < k, r * M (i + 1) ≤ M i) :
    r ^ k * M k ≤ M 0 := by
  have haux : ∀ i ≤ k, r ^ i * M i ≤ M 0 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        r ^ (i + 1) * M (i + 1) = r ^ i * (r * M (i + 1)) := by ring
        _ ≤ r ^ i * M i := mul_le_mul_of_nonneg_left (hstep i (by omega)) zero_le
        _ ≤ M 0 := ih (by omega)
  exact haux k le_rfl

/-- A unit lower bound on terminal mass converts shrinkage into a power bound.
The logarithmic restart bound below additionally requires `r > 1`. -/
theorem restart_power_le (M : ℕ → ℝ≥0) (r A : ℝ≥0) (k : ℕ)
    (hstep : ∀ i < k, r * M (i + 1) ≤ M i)
    (hterminal : 1 ≤ M k) (hinitial : M 0 ≤ A) : r ^ k ≤ A := by
  calc
    r ^ k = r ^ k * 1 := by simp
    _ ≤ r ^ k * M k := mul_le_mul_of_nonneg_left hterminal zero_le
    _ ≤ M 0 := geometric_mass_bound M r k hstep
    _ ≤ A := hinitial

/-- Exact logarithmic bound, with its required r>1 domain exposed. -/
theorem restart_log_bound (M : ℕ → ℝ≥0) (r A : ℝ≥0) (k : ℕ)
    (hr : 1 < r) (hstep : ∀ i < k, r * M (i + 1) ≤ M i)
    (hterminal : 1 ≤ M k) (hinitial : M 0 ≤ A) :
    (k : ℝ) ≤ Real.log (A : ℝ) / Real.log (r : ℝ) := by
  have hrR : 1 < (r : ℝ) := by exact_mod_cast hr
  have hpow : (r : ℝ) ^ k ≤ (A : ℝ) := by
    exact_mod_cast restart_power_le M r A k hstep hterminal hinitial
  have hlog := Real.log_le_log (pow_pos (lt_trans zero_lt_one hrR) _) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos hrR)).mpr hlog

end
end DirectedFlowCutGap.EpochAccounting
