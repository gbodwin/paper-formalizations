import DirectedFlowCutGap.CandidateOptimization
import DirectedFlowCutGap.TerminalPorts

/-!
# Finite-grid optima for bounded integer difference constraints

This module proves the integrality step needed by a constructive replacement
for the candidate LP. A common shift followed by floor preserves every integer
upper bound on a difference. Hermite's finite averaging identity then shows
that a finite grid minimum is optimal over all real feasible potentials.

The finite search space is explicit. This is not a polynomial-time optimizer:
its efficient minimum-closure implementation, and the full equivalence between
candidate path inequalities and the potential formulation, are separate tasks.
In particular no real optimizer or grid-optimality premise is assumed here.
-/

namespace DirectedFlowCutGap.CandidateGridRounding

noncomputable section
open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- A finite bounded system with integer right-hand sides. Coordinates may be
pinned by taking equal lower and upper bounds. -/
structure DifferenceSystem (I : Type*) (L : ℕ) where
  lower : I → Fin (L + 1)
  upper : I → Fin (L + 1)
  bound : I → I → ℤ

namespace DifferenceSystem

variable {L : ℕ}

/-- The real relaxation of the explicitly bounded integer system. -/
def Feasible (S : DifferenceSystem I L) (p : I → ℝ) : Prop :=
  (∀ i, (S.lower i : ℝ) ≤ p i ∧ p i ≤ (S.upper i : ℝ)) ∧
    ∀ i j, p i - p j ≤ (S.bound i j : ℝ)

/-- An integer assignment has exactly `(L+1)^|I|` possible values. -/
abbrev GridPoint (I : Type*) (L : ℕ) := I → Fin (L + 1)

def gridValue (q : GridPoint I L) : I → ℝ := fun i => (q i : ℝ)

/-- Signed costs allow the objective `sum (after - before)`. -/
def objective (c p : I → ℝ) : ℝ := ∑ i, c i * p i

/-- Every coordinate uses the same shift. Independent rounding is unsound. -/
def shiftFloor (p : I → ℝ) (d : ℝ) : I → ℝ := fun i => (⌊p i + d⌋ : ℤ)

/-- Integer difference bounds are preserved, without a sign restriction. -/
theorem floor_sub_floor_le {a b d : ℝ} {k : ℤ} (h : a - b ≤ k) :
    ⌊a + d⌋ - ⌊b + d⌋ ≤ k := by
  have hle : a + d ≤ (b + d) + k := by linarith
  have hf := Int.floor_mono hle
  rw [Int.floor_add_intCast] at hf
  omega

omit [Fintype I] in
/-- The common shift preserves bounds, equality pins, and all differences. -/
theorem shiftFloor_feasible (S : DifferenceSystem I L) {p : I → ℝ}
    (hp : S.Feasible p) {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d < 1) :
    S.Feasible (shiftFloor p d) := by
  constructor
  · intro i
    constructor
    · change (S.lower i : ℝ) ≤ (⌊p i + d⌋ : ℝ)
      have h : ((S.lower i : ℕ) : ℤ) ≤ ⌊p i + d⌋ := Int.le_floor.mpr (by
        exact_mod_cast (hp.1 i).1.trans (le_add_of_nonneg_right hd₀))
      exact_mod_cast h
    · change (⌊p i + d⌋ : ℝ) ≤ (S.upper i : ℝ)
      have h : ⌊p i + d⌋ ≤ (S.upper i : ℕ) := Int.floor_le_iff.mpr (by
        have := (hp.1 i).2
        push_cast
        linarith)
      exact_mod_cast h
  · intro i j
    change (⌊p i + d⌋ : ℝ) - (⌊p j + d⌋ : ℝ) ≤ (S.bound i j : ℝ)
    exact_mod_cast floor_sub_floor_le (d := d) (hp.2 i j)

omit [Fintype I] in
/-- Every feasible shifted floor is represented in the finite grid. -/
theorem exists_grid_shiftFloor (S : DifferenceSystem I L) {p : I → ℝ}
    (hp : S.Feasible p) {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d < 1) :
    ∃ q : GridPoint I L, gridValue q = shiftFloor p d ∧ S.Feasible (gridValue q) := by
  have hf := S.shiftFloor_feasible hp hd₀ hd₁
  have hn (i : I) : 0 ≤ ⌊p i + d⌋ := by
    have hl := (hf.1 i).1
    change (S.lower i : ℝ) ≤ (⌊p i + d⌋ : ℝ) at hl
    have hl₀ : (0 : ℝ) ≤ (S.lower i : ℝ) := Nat.cast_nonneg _
    exact_mod_cast hl₀.trans hl
  have hb (i : I) : ⌊p i + d⌋ ≤ (L : ℤ) := by
    have hu := (hf.1 i).2
    change (⌊p i + d⌋ : ℝ) ≤ (S.upper i : ℝ) at hu
    have huL : (S.upper i : ℝ) ≤ (L : ℝ) := by exact_mod_cast (Nat.le_of_lt_succ (S.upper i).isLt)
    exact_mod_cast hu.trans huL
  let q : GridPoint I L := fun i =>
    ⟨(⌊p i + d⌋).toNat, by
      have h := Int.toNat_le_toNat (hb i)
      simp only [Int.toNat_natCast] at h
      omega⟩
  have hq : gridValue q = shiftFloor p d := by
    funext i
    change ((⌊p i + d⌋).toNat : ℝ) = (⌊p i + d⌋ : ℝ)
    have h := Int.toNat_of_nonneg (hn i)
    exact_mod_cast h
  exact ⟨q, hq, by simpa only [hq] using hf⟩

/-- The search space cardinality is explicit; enumeration is exponential. -/
theorem card_grid [DecidableEq I] : Fintype.card (GridPoint I L) = (L + 1) ^ Fintype.card I := by
  simp [GridPoint]

/-- Hermite's identity computes the sum of all equally spaced common shifts. -/
theorem sum_objective_shiftFloor (c p : I → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, objective c (shiftFloor p ((j : ℝ) / N)) =
      ∑ i, c i * (⌊(N : ℝ) * p i⌋ : ℤ) := by
  unfold objective shiftFloor
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, ← Int.cast_sum, Int.sum_floor_add_div]

/-- The error in finite averaging is uniformly bounded, also for signed costs. -/
theorem objective_floor_le (c p : I → ℝ) (N : ℕ) :
    (∑ i, c i * (⌊(N : ℝ) * p i⌋ : ℤ)) ≤
      (N : ℝ) * objective c p + ∑ i, |c i| := by
  calc
    _ ≤ ∑ i, ((N : ℝ) * (c i * p i) + |c i|) := by
      apply Finset.sum_le_sum
      intro i _
      have hlow := (Int.sub_one_lt_floor ((N : ℝ) * p i)).le
      have hupp := Int.floor_le ((N : ℝ) * p i)
      by_cases hc : 0 ≤ c i
      · have hm := mul_le_mul_of_nonneg_left hupp hc
        have ha := abs_nonneg (c i)
        nlinarith
      · have hc' : c i ≤ 0 := le_of_lt (lt_of_not_ge hc)
        have hm := mul_le_mul_of_nonpos_left hlow hc'
        rw [abs_of_nonpos hc']
        nlinarith
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl

/-- A fixed averaging error vanishes when arbitrary sample counts are allowed. -/
theorem le_of_nat_mul_le_add {a b C : ℝ}
    (h : ∀ N : ℕ, 0 < N → (N : ℝ) * a ≤ (N : ℝ) * b + C) : a ≤ b := by
  by_contra hab
  have hgap : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (C / (a - b)) 0)
  have hN₀ : 0 < N := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hN)
  have hC : C < (N : ℝ) * (a - b) :=
    (div_lt_iff₀ hgap).mp (lt_of_le_of_lt (le_max_left _ _) hN)
  have := h N hN₀
  nlinarith

/-- A finite grid minimizer is no more expensive than any real feasible point.
The only minimization premise concerns an explicitly finite grid, never a real LP. -/
theorem grid_minimum_le_real (S : DifferenceSystem I L) (c : I → ℝ)
    (q : GridPoint I L)
    (hqmin : ∀ z : GridPoint I L, S.Feasible (gridValue z) →
      objective c (gridValue q) ≤ objective c (gridValue z))
    {p : I → ℝ} (hp : S.Feasible p) :
    objective c (gridValue q) ≤ objective c p := by
  apply le_of_nat_mul_le_add (C := ∑ i, |c i|)
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hshift (j : ℕ) (hj : j ∈ Finset.range N) :
      objective c (gridValue q) ≤ objective c (shiftFloor p ((j : ℝ) / N)) := by
    have hd₀ : (0 : ℝ) ≤ (j : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNR.le
    have hd₁ : (j : ℝ) / N < 1 := (div_lt_one hNR).mpr (by
      exact_mod_cast Finset.mem_range.mp hj)
    obtain ⟨z, hz, hzf⟩ := S.exists_grid_shiftFloor hp hd₀ hd₁
    simpa only [hz] using hqmin z hzf
  calc
    (N : ℝ) * objective c (gridValue q) =
        ∑ _j ∈ Finset.range N, objective c (gridValue q) := by simp
    _ ≤ ∑ j ∈ Finset.range N, objective c (shiftFloor p ((j : ℝ) / N)) :=
      Finset.sum_le_sum hshift
    _ = ∑ i, c i * (⌊(N : ℝ) * p i⌋ : ℤ) := sum_objective_shiftFloor c p N
    _ ≤ (N : ℝ) * objective c p + ∑ i, |c i| := objective_floor_le c p N

/-- A finite grid optimum exists and is optimal against every real feasible
point. Feasibility is the sole input premise; neither optimizer nor integrality
is assumed. The result does not assert polynomial running time. -/
theorem exists_grid_minimum (S : DifferenceSystem I L) (c : I → ℝ)
    (p₀ : I → ℝ) (hp₀ : S.Feasible p₀) :
    ∃ q : GridPoint I L, S.Feasible (gridValue q) ∧
      ∀ p : I → ℝ, S.Feasible p → objective c (gridValue q) ≤ objective c p := by
  classical
  obtain ⟨q₀, _, hq₀⟩ := S.exists_grid_shiftFloor hp₀ (le_refl 0) zero_lt_one
  let candidates : Finset (GridPoint I L) :=
    Finset.univ.filter fun q => S.Feasible (gridValue q)
  have hne : candidates.Nonempty := ⟨q₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₀⟩⟩
  obtain ⟨q, hq, hmin⟩ := candidates.exists_min_image (fun q => objective c (gridValue q)) hne
  refine ⟨q, (Finset.mem_filter.mp hq).2, ?_⟩
  intro p hp
  exact S.grid_minimum_le_real c q
    (fun z hz => hmin z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)) hp


/-- The unconstrained box is itself an integer difference system. -/
def boxSystem (I : Type*) (L : ℕ) : DifferenceSystem I L where
  lower := fun _ => ⟨0, Nat.zero_lt_succ _⟩
  upper := fun _ => ⟨L, Nat.lt_succ_self _⟩
  bound := fun _ _ => (L : ℤ)

omit [Fintype I] in
theorem feasible_boxSystem {p : I → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ (L : ℝ)) :
    (boxSystem I L).Feasible p := by
  refine ⟨?_, ?_⟩
  · simpa [boxSystem] using hp
  · intro i j
    have hi := hp i
    have hj := hp j
    dsimp [boxSystem]
    push_cast
    linarith

/-- A reusable form for explicitly described finite constraint families. The
hypotheses require only boundedness and the elementary common-shift closure
property, never an optimizer, an optimum value, or a grid-optimality assertion. -/
theorem exists_grid_minimum_of_shift_closed (P : (I → ℝ) → Prop)
    (hbounded : ∀ p, P p → ∀ i, 0 ≤ p i ∧ p i ≤ (L : ℝ))
    (hshift : ∀ p, P p → ∀ d : ℝ, 0 ≤ d → d < 1 → P (shiftFloor p d))
    (c : I → ℝ) (p₀ : I → ℝ) (hp₀ : P p₀) :
    ∃ q : GridPoint I L, P (gridValue q) ∧
      ∀ p : I → ℝ, P p → objective c (gridValue q) ≤ objective c p := by
  classical
  have hex (p : I → ℝ) (hp : P p) (d : ℝ) (hd₀ : 0 ≤ d) (hd₁ : d < 1) :
      ∃ q : GridPoint I L, gridValue q = shiftFloor p d ∧ P (gridValue q) := by
    obtain ⟨q, hq, _⟩ := (boxSystem I L).exists_grid_shiftFloor
      (feasible_boxSystem (hbounded p hp)) hd₀ hd₁
    exact ⟨q, hq, by simpa only [hq] using hshift p hp d hd₀ hd₁⟩
  obtain ⟨q₀, _, hq₀⟩ := hex p₀ hp₀ 0 le_rfl zero_lt_one
  let candidates : Finset (GridPoint I L) := Finset.univ.filter fun q => P (gridValue q)
  have hne : candidates.Nonempty := ⟨q₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₀⟩⟩
  obtain ⟨q, hq, hmin⟩ := candidates.exists_min_image (fun q => objective c (gridValue q)) hne
  refine ⟨q, (Finset.mem_filter.mp hq).2, ?_⟩
  intro p hp
  apply le_of_nat_mul_le_add (C := ∑ i, |c i|)
  intro N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow (j : ℕ) (hj : j ∈ Finset.range N) :
      objective c (gridValue q) ≤ objective c (shiftFloor p ((j : ℝ) / N)) := by
    have hd₀ : (0 : ℝ) ≤ (j : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNR.le
    have hd₁ : (j : ℝ) / N < 1 := (div_lt_one hNR).mpr (by
      exact_mod_cast Finset.mem_range.mp hj)
    obtain ⟨z, hz, hzf⟩ := hex p hp ((j : ℝ) / N) hd₀ hd₁
    have hzmem : z ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzf⟩
    simpa only [hz] using hmin z hzmem
  calc
    (N : ℝ) * objective c (gridValue q) =
        ∑ _j ∈ Finset.range N, objective c (gridValue q) := by simp
    _ ≤ ∑ j ∈ Finset.range N, objective c (shiftFloor p ((j : ℝ) / N)) :=
      Finset.sum_le_sum hlow
    _ = ∑ i, c i * (⌊(N : ℝ) * p i⌋ : ℤ) := sum_objective_shiftFloor c p N
    _ ≤ (N : ℝ) * objective c p + ∑ i, |c i| := objective_floor_le c p N

end DifferenceSystem
end
end DirectedFlowCutGap.CandidateGridRounding
