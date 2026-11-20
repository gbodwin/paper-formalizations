import DirectedFlowCutGap.FiniteHarmonicThreshold
import Mathlib.Data.List.MinMax

/-! Select a positive rational distance maximizing threshold times the number
of demands it reaches. The finite harmonic estimate is for the selected
distance itself, and ties at the threshold are counted. -/
namespace DirectedFlowCutGap.RationalHarmonicThreshold

open scoped BigOperators NNReal NNRat
open FiniteHarmonicThreshold

def count {m : ℕ} (d : Fin m → ℚ≥0) (threshold : ℚ≥0) : ℕ :=
  (Finset.univ.filter fun i => threshold ≤ d i).card

def score {m : ℕ} (d : Fin m → ℚ≥0) (i : Fin m) : ℚ≥0 :=
  d i*(count d (d i) : ℚ≥0)

def choose {m : ℕ} (d : Fin m → ℚ≥0) : Option (Fin m) :=
  (List.finRange m).argmax (score d)

theorem choose_max {m : ℕ} (d : Fin m → ℚ≥0) {i : Fin m} (chosen : choose d=some i) (j : Fin m) :
    score d j ≤ score d i := by
  apply List.le_of_mem_argmax (List.mem_finRange j)
  change i ∈ choose d
  simp only [chosen,Option.mem_some_iff]

theorem count_cast {m : ℕ} (d : Fin m → ℚ≥0) (threshold : ℚ≥0) :
    count d threshold = (above (fun i => (d i : ℝ≥0)) (threshold : ℝ≥0)).card := by
  unfold count above
  congr 1
  ext i
  simp

theorem choose_spec {m : ℕ} (d : Fin m → ℚ≥0) (positive : 0<∑ i, (d i : ℝ≥0)) :
    ∃ i, choose d=some i ∧ 0<d i ∧ 0<count d (d i) ∧
      (∑ j, (d j : ℝ≥0)) ≤ harmonicWeight m*((d i : ℝ≥0)*(count d (d i) : ℝ≥0)) := by
  classical
  let D (i : Fin m) : ℝ≥0 := d i
  obtain ⟨τ,pos,nonempty,bound⟩ := exists_threshold D positive
  obtain ⟨j,hj,minimum⟩ := Finset.exists_min_image (above D τ) D (Finset.card_pos.mp nonempty)
  have reached : τ ≤ D j := (Finset.mem_filter.mp hj).2
  have cover : above D τ ⊆ above D (D j) := by
    intro k included
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,minimum k included⟩
  have counts : ((above D τ).card : ℝ≥0)≤(count d (d j) : ℝ≥0) := by
    rw [count_cast]
    exact_mod_cast Finset.card_le_card cover
  have witness : τ*((above D τ).card : ℝ≥0)≤(score d j : ℝ≥0) := by
    unfold score
    push_cast
    exact mul_le_mul' reached counts
  cases picked : choose d with
  | none =>
    rw [choose,List.argmax_eq_none] at picked
    have impossible := List.mem_finRange j
    rw [picked] at impossible
    exact (List.not_mem_nil impossible).elim
  | some i =>
    have compare : (score d j : ℝ≥0)≤(score d i : ℝ≥0) := by
      exact_mod_cast choose_max d picked j
    have bound' := bound.trans (mul_le_mul_of_nonneg_left (witness.trans compare) zero_le)
    rw [Fintype.card_fin] at bound'
    have score_pos : 0<score d i := by
      by_contra h
      have zero : score d i=0 := le_antisymm (le_of_not_gt h) zero_le
      simp only [zero,NNRat.cast_zero,mul_zero,D] at bound'
      exact (not_le_of_gt positive) bound'
    refine ⟨i,rfl,?_,?_,?_⟩
    · unfold score at score_pos
      exact pos_of_mul_pos_left score_pos zero_le
    · unfold score at score_pos
      exact_mod_cast (pos_of_mul_pos_right score_pos zero_le : (0 : ℚ≥0)<(count d (d i) : ℚ≥0))
    · simpa only [D,score,NNRat.cast_mul,NNRat.cast_natCast] using bound'

end DirectedFlowCutGap.RationalHarmonicThreshold
