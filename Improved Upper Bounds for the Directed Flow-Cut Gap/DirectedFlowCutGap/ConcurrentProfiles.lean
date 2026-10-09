import DirectedFlowCutGap.IntegerPackingCovering
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Concurrent flows and finite joint path profiles

A demand has a finite type of actual paths. Path/resource incidences are natural
numbers, so resources used by several paths in a profile count several times.
A joint profile chooses one path for every demand. Its packing mass is common
per-demand throughput, not the sum over all demand flows.

The product construction below proves the equivalence with independent path
amounts: a positive common throughput gives a finite joint product distribution,
and marginalization recovers the original path amounts. Zero throughput and
unreachable demands are handled without dividing by zero.
-/

namespace DirectedFlowCutGap.ConcurrentProfiles
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {R D : Type*} [Fintype D]
variable {Path : D → Type*} [∀ d, Fintype (Path d)]

abbrev Profile (Path : D → Type*) := ∀ d, Path d
abbrev Flow (Path : D → Type*) := ∀ d, Path d → ℝ

/-- Multiplicity, including repeated use of the same resource by distinct demands. -/
def profileIncidence (a : ∀ d, R → Path d → ℕ) (r : R) (q : Profile Path) : ℕ :=
  ∑ d, a d r (q d)

/-- Actual resource load of a family of path amounts. -/
def load (a : ∀ d, R → Path d → ℕ) (f : Flow Path) (r : R) : ℝ :=
  ∑ d, ∑ p, (a d r p : ℝ) * f d p

/-- Equal common throughput; excess per-demand flow may be discarded. -/
def IsConcurrent (a : ∀ d, R → Path d → ℕ) (c : R → ℝ)
    (f : Flow Path) (t : ℝ) : Prop :=
  0 ≤ t ∧ (∀ d p, 0 ≤ f d p) ∧ (∀ d, ∑ p, f d p = t) ∧ ∀ r, load a f r ≤ c r

/-- The conventional minimum-demand formulation, allowing excess flow. -/
def IsAtLeastConcurrent (a : ∀ d, R → Path d → ℕ) (c : R → ℝ)
    (f : Flow Path) (t : ℝ) : Prop :=
  0 ≤ t ∧ (∀ d p, 0 ≤ f d p) ∧ (∀ d, t ≤ ∑ p, f d p) ∧ ∀ r, load a f r ≤ c r

/-- Per-demand path marginals of joint profile amounts. -/
def marginal (F : Profile Path → ℝ) (d : D) (p : Path d) : ℝ :=
  ∑ q, if q d = p then F q else 0

theorem marginal_nonneg {F : Profile Path → ℝ} (hF : ∀ q, 0 ≤ F q)
    (d : D) (p : Path d) : 0 ≤ marginal F d p := by
  apply Finset.sum_nonneg
  intro q _
  exact ite_nonneg (hF q) (le_refl 0)

theorem sum_marginal (F : Profile Path → ℝ) (d : D) :
    ∑ p, marginal F d p = ∑ q, F q := by
  classical
  unfold marginal
  rw [Finset.sum_comm]
  simp

/-- Marginalization preserves the full resource load with multiplicity. -/
theorem load_marginal (a : ∀ d, R → Path d → ℕ) (F : Profile Path → ℝ) (r : R) :
    load a (marginal F) r = IntegerPackingCovering.load (profileIncidence a) F r := by
  classical
  unfold load marginal IntegerPackingCovering.load profileIncidence
  simp only [Finset.mul_sum, Nat.cast_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [mul_ite, mul_zero]
  simp

/-- Every feasible joint packing gives a genuine concurrent path flow. -/
theorem marginal_isConcurrent (a : ∀ d, R → Path d → ℕ) {c : R → ℝ}
    {F : Profile Path → ℝ} (hF : IntegerPackingCovering.IsPacking (profileIncidence a) c F) :
    IsConcurrent a c (marginal F) (IntegerPackingCovering.packingValue F) := by
  refine ⟨Finset.sum_nonneg (fun q _ => hF.1 q), marginal_nonneg hF.1,
    sum_marginal F, ?_⟩
  intro r
  rw [load_marginal]
  exact hF.2 r

/-- Marginals of a finite product of unit-mass distributions. -/
theorem product_marginal (f : Flow Path) (hf : ∀ d, ∑ p, f d p = 1)
    (d : D) (p : Path d) :
    marginal (fun q => ∏ i, f i (q i)) d p = f d p := by
  classical
  let g : Flow Path := Function.update f d (fun x => if x = p then f d x else 0)
  have hp : ∀ q : Profile Path,
      (if q d = p then ∏ i, f i (q i) else 0) = ∏ i, g i (q i) := by
    intro q
    by_cases h : q d = p
    · rw [ite_eq_left h]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i = d
      · subst i
        simp [g, h]
      · simp [g, hi]
    · rw [ite_eq_right h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp [g, h])
  calc
    marginal (fun q => ∏ i, f i (q i)) d p = ∑ q : Profile Path, ∏ i, g i (q i) := by
      unfold marginal
      exact Finset.sum_congr rfl (fun q _ => hp q)
    _ = ∏ i, ∑ x, g i x := (Fintype.prod_sum g).symm
    _ = ∑ x, g d x := by
      apply Finset.prod_eq_single d
      · intro i _ hi
        simpa [g, hi] using hf i
      · simp
    _ = f d p := by simp [g]

/-- Unit total mass of the finite product construction. -/
theorem sum_product (f : Flow Path) (hf : ∀ d, ∑ p, f d p = 1) :
    ∑ q : Profile Path, ∏ d, f d (q d) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [hf]

/-- Finite joint product decomposition, including the zero-throughput case. -/
theorem exists_profile_packing (a : ∀ d, R → Path d → ℕ) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) {f : Flow Path} {t : ℝ} (hf : IsConcurrent a c f t) :
    ∃ F : Profile Path → ℝ, IntegerPackingCovering.IsPacking (profileIncidence a) c F ∧
      IntegerPackingCovering.packingValue F = t := by
  classical
  by_cases ht : t = 0
  · subst t
    exact ⟨0, IntegerPackingCovering.zero_isPacking _ hc, by simp [IntegerPackingCovering.packingValue]⟩
  let g : Flow Path := fun d p => f d p / t
  have hg : ∀ d, ∑ p, g d p = 1 := by
    intro d
    simp only [g, ← Finset.sum_div, hf.2.2.1 d, div_self ht]
  let F : Profile Path → ℝ := fun q => t * ∏ d, g d (q d)
  have hm : marginal F = f := by
    funext d p
    calc
      marginal F d p = t * marginal (fun q => ∏ i, g i (q i)) d p := by
        simp [marginal, F, Finset.mul_sum, mul_ite]
      _ = t * g d p := by rw [product_marginal g hg]
      _ = f d p := by dsimp [g]; field_simp
  refine ⟨F, ⟨fun q => mul_nonneg hf.1 (Finset.prod_nonneg fun d _ =>
    div_nonneg (hf.2.1 d (q d)) hf.1), ?_⟩, ?_⟩
  · intro r
    rw [← load_marginal, hm]
    exact hf.2.2.2 r
  · simp [IntegerPackingCovering.packingValue, F, ← Finset.mul_sum, sum_product g hg]

/-- Exact LP identification, not an assumption about duality. -/
theorem concurrent_iff_profile_packing (a : ∀ d, R → Path d → ℕ) {c : R → ℝ}
    (hc : ∀ r, 0 ≤ c r) (t : ℝ) :
    (∃ f, IsConcurrent a c f t) ↔
      ∃ F, IntegerPackingCovering.IsPacking (profileIncidence a) c F ∧
        IntegerPackingCovering.packingValue F = t := by
  constructor
  · rintro ⟨f, hf⟩
    exact exists_profile_packing a hc hf
  · rintro ⟨F, hF, rfl⟩
    exact ⟨marginal F, marginal_isConcurrent a hF⟩

/-- Discarding excess flow identifies equal-throughput and minimum-throughput
formulations, even when some demand has zero total flow. -/
theorem trim_atLeastConcurrent (a : ∀ d, R → Path d → ℕ) {c : R → ℝ}
    {f : Flow Path} {t : ℝ} (hf : IsAtLeastConcurrent a c f t) :
    ∃ g, IsConcurrent a c g t := by
  classical
  let g : Flow Path := fun d p => (t / (∑ q, f d q)) * f d p
  have htotal : ∀ d, 0 ≤ ∑ p, f d p :=
    fun d => Finset.sum_nonneg (fun p _ => hf.2.1 d p)
  have hfactor : ∀ d, t / (∑ p, f d p) ≤ 1 := by
    intro d
    by_cases h : (∑ p, f d p) = 0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne (htotal d) (Ne.symm h))).mpr (hf.2.2.1 d)
  refine ⟨g, hf.1, fun d p => mul_nonneg (div_nonneg hf.1 (htotal d)) (hf.2.1 d p),
    ?_, ?_⟩
  · intro d
    by_cases h : (∑ p, f d p) = 0
    · have ht : t = 0 := le_antisymm (by simpa [h] using hf.2.2.1 d) hf.1
      simp [g, ht]
    · simp only [g, ← Finset.mul_sum, div_mul_cancel₀ _ h]
  · intro r
    apply le_trans _ (hf.2.2.2 r)
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact (mul_le_mul_of_nonneg_right (hfactor d) (hf.2.1 d p)).trans_eq (one_mul _)

/-- Equal-throughput optima maximize the conventional minimum-demand objective. -/
theorem exists_concurrent_iff_atLeast (a : ∀ d, R → Path d → ℕ) (c : R → ℝ) (t : ℝ) :
    (∃ f, IsConcurrent a c f t) ↔ ∃ f, IsAtLeastConcurrent a c f t := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, hf.1, hf.2.1, fun d => (hf.2.2.1 d).ge, hf.2.2.2⟩
  · rintro ⟨f, hf⟩
    exact trim_atLeastConcurrent a hf

/-- Any unreachable demand forces common throughput to be zero. -/
theorem throughput_eq_zero_of_empty_path (a : ∀ d, R → Path d → ℕ) {c : R → ℝ}
    {f : Flow Path} {t : ℝ} (hf : IsConcurrent a c f t)
    (d : D) [IsEmpty (Path d)] : t = 0 := by
  simpa using (hf.2.2.1 d).symm

/-- The conventional minimum-throughput objective is also zero when one demand
is unreachable, regardless of whether the other demands can carry flow. -/
theorem atLeast_throughput_eq_zero_of_empty_path (a : ∀ d, R → Path d → ℕ) {c : R → ℝ}
    {f : Flow Path} {t : ℝ} (hf : IsAtLeastConcurrent a c f t)
    (d : D) [IsEmpty (Path d)] : t = 0 := by
  apply le_antisymm _ hf.1
  simpa using hf.2.2.1 d

/-- Zero flow is feasible for every nonnegative capacity assignment, even when
some demands have no paths or the demand family itself is empty. -/
theorem zero_isConcurrent (a : ∀ d, R → Path d → ℕ) {c : R → ℝ} (hc : ∀ r, 0 ≤ c r) :
    IsConcurrent a c (fun _ _ => 0) 0 := by
  refine ⟨le_rfl, fun _ _ => le_rfl, fun _ => by simp, ?_⟩
  simpa [load] using hc

end
end DirectedFlowCutGap.ConcurrentProfiles
