import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Greedy thinning with honest deleted-weight accounting

This is a numerical replacement for the charging argument on printed pages
20–21 (Lemma 26) of arXiv:2604.03412v3. A nondeleted index skipped by thinning
is controlled by the failed selection threshold. It is never counted as a
deleted index. Distances may decrease arbitrarily; only their one-step upper
increments are bounded.

`scan d deleted h n` processes indices `0, ..., n-1`. The final value in the
potential estimate is `d n`. Thus `w i` is the increment budget from `i` to
`i+1`, and only genuinely deleted indices contribute to `deletedWeight`.
Graph-prefix selection, endpoint accounting, and path-system assembly are
separate obligations; this file does not assert the full graph lemma.
-/

namespace DirectedFlowCutGap.WitnessThinning

open scoped BigOperators Classical

/-- The actual state of the greedy scan. -/
structure State where
  last : ℝ
  selected : List ℕ

/-- Scan in index order, appending exactly the nondeleted threshold crossings.
The initial virtual selected value is `-h`. -/
noncomputable def scan (d : ℕ → ℝ) (deleted : ℕ → Prop) (h : ℝ) : ℕ → State := by
  classical
  exact fun
    | 0 => ⟨-h, []⟩
    | n + 1 =>
      let s := scan d deleted h n
      if ¬deleted n ∧ s.last + h ≤ d n then
        ⟨d n, s.selected ++ [n]⟩
      else s

/-- Weight of actually deleted indices in the processed prefix. -/
noncomputable def deletedWeight (w : ℕ → ℝ) (deleted : ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact ∑ i ∈ Finset.range n, if deleted i then w i else 0

@[simp] theorem scan_zero (d : ℕ → ℝ) (deleted : ℕ → Prop) (h : ℝ) :
    scan d deleted h 0 = ⟨-h, []⟩ := rfl

@[simp] theorem deletedWeight_zero (w : ℕ → ℝ) (deleted : ℕ → Prop) :
    deletedWeight w deleted 0 = 0 := by simp [deletedWeight]

theorem deletedWeight_succ (w : ℕ → ℝ) (deleted : ℕ → Prop) (n : ℕ) :
    deletedWeight w deleted (n + 1) =
      deletedWeight w deleted n + (if deleted n then w n else 0) := by
  classical
  simp [deletedWeight, Finset.sum_range_succ]

/-- Every selected index belongs to the processed prefix and avoids deletion. -/
theorem selected_mem (d : ℕ → ℝ) (deleted : ℕ → Prop) (h : ℝ) (n : ℕ) :
    ∀ i ∈ (scan d deleted h n).selected, i < n ∧ ¬deleted i := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [scan]
    split_ifs with hs
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact ⟨Nat.lt_succ_of_lt (ih i hi).1, (ih i hi).2⟩
      · have he : i = n := List.mem_singleton.mp hi
        subst i
        exact ⟨Nat.lt_succ_self n, hs.1⟩
    · intro i hi
      exact ⟨Nat.lt_succ_of_lt (ih i hi).1, (ih i hi).2⟩

/-- The construction selects indices in strictly increasing order. -/
theorem selected_increasing (d : ℕ → ℝ) (deleted : ℕ → Prop) (h : ℝ) (n : ℕ) :
    (scan d deleted h n).selected.Pairwise (· < ·) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [scan]
    split_ifs with hs
    · apply List.pairwise_append.mpr
      refine ⟨ih, by simp, ?_⟩
      intro i hi j hj
      have he : j = n := List.mem_singleton.mp hj
      subst j
      exact (selected_mem d deleted h n i hi).1
    · exact ih

/-- All selected values are bounded by the current last selected value. -/
theorem selected_le_last (d : ℕ → ℝ) (deleted : ℕ → Prop) {h : ℝ}
    (hh : 0 ≤ h) (n : ℕ) :
    ∀ i ∈ (scan d deleted h n).selected, d i ≤ (scan d deleted h n).last := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [scan]
    split_ifs with hs
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · have := ih i hi
        linarith [hs.2]
      · have he : i = n := List.mem_singleton.mp hi
        subst i
        exact le_rfl
    · exact ih

/-- Values at any two selected positions are separated by at least `h`. -/
theorem selected_separated (d : ℕ → ℝ) (deleted : ℕ → Prop) {h : ℝ}
    (hh : 0 ≤ h) (n : ℕ) :
    (scan d deleted h n).selected.Pairwise (fun i j => d i + h ≤ d j) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [scan]
    split_ifs with hs
    · apply List.pairwise_append.mpr
      refine ⟨ih, by simp, ?_⟩
      intro i hi j hj
      have he : j = n := List.mem_singleton.mp hj
      subst j
      have := selected_le_last d deleted hh n i hi
      linarith [hs.2]
    · exact ih

/-- Counting the selected threshold crossings gives a lower bound on `last`. -/
theorem count_mul_step_le (d : ℕ → ℝ) (deleted : ℕ → Prop) (h : ℝ) (n : ℕ) :
    ((scan d deleted h n).selected.length : ℝ) * h ≤ (scan d deleted h n).last + h := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [scan]
    split_ifs with hs
    · simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      nlinarith [hs.2]
    · exact ih

/-- An upper bound on all processed values also bounds the last selected value. -/
theorem last_le (d : ℕ → ℝ) (deleted : ℕ → Prop) (h M : ℝ) (n : ℕ)
    (hinit : -h ≤ M) (hd : ∀ i < n, d i ≤ M) :
    (scan d deleted h n).last ≤ M := by
  classical
  induction n with
  | zero => exact hinit
  | succ n ih =>
    simp only [scan]
    split_ifs with hs
    · exact hd n (Nat.lt_succ_self n)
    · exact ih (fun i hi => hd i (Nat.lt_succ_of_lt hi))

/-- The key honest-charging invariant. Deleted steps charge their own weight;
a skipped nondeleted index is controlled by its failed threshold test. -/
theorem scan_potential (d w : ℕ → ℝ) (deleted : ℕ → Prop) {h U : ℝ}
    (hh : 0 ≤ h) (hU : 0 ≤ U) (hzero : d 0 = 0) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i ∧ w i ≤ U)
    (hd : ∀ i < n, d (i + 1) ≤ d i + w i) :
    (scan d deleted h n).last ≤
        ((scan d deleted h n).selected.length : ℝ) * (h + U) +
          deletedWeight w deleted n - h ∧
      d n ≤ ((scan d deleted h n).selected.length : ℝ) * (h + U) +
          deletedWeight w deleted n + U := by
  classical
  induction n with
  | zero => simp [hzero, hU]
  | succ n ih =>
    obtain ⟨hlast, hcur⟩ := ih
      (fun i hi => hw i (Nat.lt_succ_of_lt hi))
      (fun i hi => hd i (Nat.lt_succ_of_lt hi))
    obtain ⟨hwn, hwU⟩ := hw n (Nat.lt_succ_self n)
    have hnext := hd n (Nat.lt_succ_self n)
    rw [deletedWeight_succ]
    by_cases hdel : deleted n
    · have hs : ¬(¬deleted n ∧ (scan d deleted h n).last + h ≤ d n) :=
        fun hs => hs.1 hdel
      simp only [scan, ite_eq_right hs, ite_eq_left hdel]
      constructor <;> linarith
    · by_cases hsel : (scan d deleted h n).last + h ≤ d n
      · have hs : ¬deleted n ∧ (scan d deleted h n).last + h ≤ d n := ⟨hdel, hsel⟩
        simp only [scan, ite_eq_left hs, ite_eq_right hdel, List.length_append,
          List.length_singleton, Nat.cast_add, Nat.cast_one]
        constructor <;> nlinarith
      · have hs : ¬(¬deleted n ∧ (scan d deleted h n).last + h ≤ d n) :=
          fun hs => hsel hs.2
        simp only [scan, ite_eq_right hs, ite_eq_right hdel]
        have hskip : d n < (scan d deleted h n).last + h := lt_of_not_ge hsel
        constructor <;> linarith

/-- Finite greedy thinning, with no monotonicity assumption on the distances. -/
theorem final_distance_le (d w : ℕ → ℝ) (deleted : ℕ → Prop) {h U : ℝ}
    (hh : 0 ≤ h) (hU : 0 ≤ U) (hzero : d 0 = 0) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i ∧ w i ≤ U)
    (hd : ∀ i < n, d (i + 1) ≤ d i + w i) :
    d n ≤ deletedWeight w deleted n +
      (((scan d deleted h n).selected.length : ℝ) + 1) * (h + U) := by
  have hp := (scan_potential d w deleted hh hU hzero n hw hd).2
  nlinarith

/-- The conservative source-scale constants follow from the proved potential.
The deleted-weight allowance includes two possible endpoint weights. -/
theorem source_scale_arithmetic {q L B δ terminal : ℝ}
    (hq : 0 ≤ q) (hB : 1 ≤ B) (hL : 64 * B ≤ L)
    (hterminal : 1 - B / L ≤ terminal)
    (hdeleted : δ ≤ 1 / 4 + 2 * (B / L))
    (hpotential : terminal ≤ δ + (q + 1) * (1 / L + B / L)) :
    L / (4 * B) ≤ q - 1 := by
  have hBpos : 0 < B := by linarith
  have hLpos : 0 < L := by nlinarith
  have hcombined : (3 : ℝ) / 4 ≤ (q + 1) * (1 / L + B / L) + 3 * (B / L) := by
    linarith
  have heq : (q + 1) * (1 / L + B / L) + 3 * (B / L) =
      ((q + 1) * (1 + B) + 3 * B) / L := by ring
  rw [heq] at hcombined
  have hscaled := (le_div_iff₀ hLpos).mp hcombined
  apply (div_le_iff₀ (by positivity : 0 < 4 * B)).mpr
  have hprod : 0 ≤ (q + 1) * (B - 1) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- With `h = 1/L` and `U = B/L`, the actual greedy output has the
source-compatible number of edges. All distance upper bounds are explicit;
in the graph application they must come from an appropriate prefix. -/
theorem source_scale_bounds (d w : ℕ → ℝ) (deleted : ℕ → Prop)
    (n : ℕ) {L B : ℝ} (hB : 1 ≤ B) (hL : 64 * B ≤ L)
    (hzero : d 0 = 0)
    (hw : ∀ i < n, 0 ≤ w i ∧ w i ≤ B / L)
    (hd : ∀ i < n, d (i + 1) ≤ d i + w i)
    (hterminal : 1 - B / L ≤ d n)
    (hdeleted : deletedWeight w deleted n ≤ 1 / 4 + 2 * (B / L))
    (hbounded : ∀ i < n, d i ≤ 1) :
    let selected := (scan d deleted (1 / L) n).selected
    selected ≠ [] ∧ L / (4 * B) ≤ ((selected.length - 1 : ℕ) : ℝ) ∧
      ((selected.length - 1 : ℕ) : ℝ) ≤ L := by
  have hBpos : 0 < B := by linarith
  have hLpos : 0 < L := by nlinarith
  have hh : 0 ≤ 1 / L := by positivity
  have hU : 0 ≤ B / L := by positivity
  have hp := final_distance_le d w deleted hh hU hzero n hw hd
  have hlo := source_scale_arithmetic
    (q := ((scan d deleted (1 / L) n).selected.length : ℝ))
    (Nat.cast_nonneg _) hB hL hterminal hdeleted hp
  have hcount := count_mul_step_le d deleted (1 / L) n
  have hlast := last_le d deleted (1 / L) 1 n (by linarith) hbounded
  have hratio : 0 < L / (4 * B) := by positivity
  have hlen_real : 1 ≤ ((scan d deleted (1 / L) n).selected.length : ℝ) := by
    linarith
  have hlen : 1 ≤ (scan d deleted (1 / L) n).selected.length := by exact_mod_cast hlen_real
  have hcast : (((scan d deleted (1 / L) n).selected.length - 1 : ℕ) : ℝ) =
      ((scan d deleted (1 / L) n).selected.length : ℝ) - 1 := by
    simp only [Nat.cast_sub hlen, Nat.cast_one]
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro hempty
    rw [hempty] at hlen
    simp at hlen
  · rw [hcast]
    exact hlo
  · rw [hcast]
    have hdiv : (((scan d deleted (1 / L) n).selected.length : ℝ) - 1) / L ≤ 1 := by
      calc
        _ = ((scan d deleted (1 / L) n).selected.length : ℝ) * (1 / L) - 1 / L := by ring
        _ ≤ 1 := by linarith
    have := (div_le_iff₀ hLpos).mp hdiv
    simpa using this

end DirectedFlowCutGap.WitnessThinning
