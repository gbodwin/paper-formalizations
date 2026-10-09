import DirectedFlowCutGap.FractionalCoverCore

/-!
# Direct analysis of the rational 0/1 recurrence

Logarithms are proof devices only. The proof uses the actual bottleneck ratio
`b/c ≤ 1`; it does not import a general packing theorem or silently discard its
entry/capacity normalization hypothesis. The comparator is any feasible cover.
-/
namespace DirectedFlowCutGap.FractionalCover
open scoped BigOperators

lemma log_half_update_lower {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 3 ≤ Real.log (1 + u / 2) := by
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + u / 2 by linarith)
  have hinv : (1 + u / 2)⁻¹ ≤ 1 - u / 3 := by
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 + u / 2)).2
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]
  have hi : u / 3 ≤ 1 - (1 + u / 2)⁻¹ := by linarith
  exact hi.trans hl

lemma potential_step {D a b z : ℝ} (hD : 0 < D) (ha : 0 < a)
    (hb : 0 ≤ b) (hz : 0 < z) (hza : z ≤ D / a) :
    2 * z * (Real.log (D + b * a / 2) - Real.log D) ≤ b := by
  have hnew : 0 < D + b * a / 2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hnew hD)
  rw [Real.log_div (ne_of_gt hnew) (ne_of_gt hD)] at hlog
  have hratio : (D + b * a / 2) / D - 1 ≤ b / (2 * z) := by
    have hzD : z * a ≤ D := (le_div_iff₀ ha).mp hza
    have hbz := mul_le_mul_of_nonneg_left hzD hb
    calc
      _ = b * a / (2 * D) := by field_simp; ring
      _ ≤ b / (2 * z) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
  have h := (le_div_iff₀ (show 0 < 2 * z by positivity)).mp (hlog.trans hratio)
  nlinarith

lemma load_step {c x b : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    b ≤ 3 * c * (Real.log (x * (1 + b / (2 * c))) - Real.log x) := by
  have hu : 0 ≤ b / c := div_nonneg hb hc.le
  have hu1 : b / c ≤ 1 := (div_le_one₀ hc).2 hbc
  have hl := log_half_update_lower hu hu1
  have heq : b / c / 2 = b / (2 * c) := by ring
  rw [heq] at hl
  rw [Real.log_mul (ne_of_gt hx) (by positivity : 1 + b / (2 * c) ≠ 0)]
  have := mul_le_mul_of_nonneg_left hl (show 0 ≤ 3 * c by positivity)
  field_simp at this ⊢
  nlinarith

/-- Proof-only analytic quantities associated with the executable state. -/
structure AnalyticInvariant {m : ℕ} (c : Row m) (s : State m) : Prop where
  potential : ∀ z : ℝ, 0 < z → z ≤ (s.bestCost : ℝ) →
    2 * z * (Real.log (objective c s.weights : ℝ) -
      Real.log (objective c (initial c) : ℝ)) ≤ (s.total : ℝ)
  load : ∀ i, (value s.loads i : ℝ) ≤ 3 * (value c i : ℝ) *
    (Real.log (value c i * value s.weights i : ℚ) - Real.log (delta m : ℝ))

lemma start_analytic {m : ℕ} (c : Row m) (oracle : Oracle m)
    (hc : ∀ i, 0 < value c i) : AnalyticInvariant c (start c oracle) := by
  constructor
  · intro z _ _
    simp [start]
  · intro i
    simp [start, initial_scaled c hc]

lemma step_analytic {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) {s : State m}
    (hs : BasicInvariant c columns s) (ha : AnalyticInvariant c s) :
    AnalyticInvariant c (step c oracle s) := by
  unfold step
  split_ifs with hstop
  · exact ha
  · have hy := hs.positive
    have hlen := length_pos hy ⟨_, ho.bottleneck_mem _ hy⟩
    have hobj := objective_pos c _ hm hc hy
    constructor
    · intro z hz hzbest
      have hzold : z ≤ (s.bestCost : ℝ) := by
        exact hzbest.trans (by exact_mod_cast (min_le_right
          (objective c (normalized s.weights (oracle s.weights).column)) s.bestCost))
      have hzcurrent : z ≤ (objective c s.weights : ℝ) /
          (length s.weights (oracle s.weights).column : ℝ) := by
        have hh : z ≤ (objective c (normalized s.weights (oracle s.weights).column) : ℝ) :=
          hzbest.trans (by exact_mod_cast (min_le_left
            (objective c (normalized s.weights (oracle s.weights).column)) s.bestCost))
        rw [objective_normalized] at hh
        exact_mod_cast hh
      have hp := potential_step (by exact_mod_cast hobj) (by exact_mod_cast hlen)
        (show 0 ≤ (value c (oracle s.weights).bottleneck : ℝ) by exact_mod_cast (hc _).le)
        hz hzcurrent
      have heq : (objective c (update c s.weights (oracle s.weights)) : ℝ) =
          (objective c s.weights : ℝ) +
          (value c (oracle s.weights).bottleneck : ℝ) *
            (length s.weights (oracle s.weights).column : ℝ) / 2 := by
        exact_mod_cast objective_update c s.weights (oracle s.weights) hc
      dsimp
      rw [heq]
      push_cast
      linarith [ha.potential z hz hzold]
    · intro i
      have hci : (0 : ℝ) < value c i := by exact_mod_cast hc i
      have hxi : (0 : ℝ) < (value c i * value s.weights i : ℚ) := by
        exact_mod_cast mul_pos (hc i) (hy i)
      dsimp
      simp only [value_ofFn]
      by_cases hi : i ∈ (oracle s.weights).column
      · rw [ite_eq_left hi]
        have hl := load_step hci hxi
          (show 0 ≤ (value c (oracle s.weights).bottleneck : ℝ) by exact_mod_cast (hc _).le)
          (show (value c (oracle s.weights).bottleneck : ℝ) ≤ value c i by
            exact_mod_cast ho.bottleneck_min _ hy i hi)
        have heq : ((value c i * value (update c s.weights (oracle s.weights)) i : ℚ) : ℝ) =
            ((value c i * value s.weights i : ℚ) : ℝ) *
              (1 + (value c (oracle s.weights).bottleneck : ℝ) / (2 * (value c i : ℝ))) := by
          simp only [update, value_ofFn, ite_eq_left hi]
          push_cast
          ring
        rw [heq]
        push_cast at hl ⊢
        have hold := ha.load i
        push_cast at hold
        linarith
      · rw [ite_eq_right hi]
        simpa [update, hi] using ha.load i

lemma run_analytic {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (n : ℕ) : AnalyticInvariant c (run c oracle n) := by
  induction n with
  | zero => exact start_analytic c oracle hc
  | succ n ih =>
    exact step_analytic c columns oracle hm hc ho
      (run_invariant c columns oracle hm hc ho n) ih

lemma log_parameters {m : ℕ} (hm : 0 < m) :
    -Real.log ((m : ℝ) * (delta m : ℝ)) = Real.log (3 * (m : ℝ) / 2) ∧
    Real.log (3 / 2 : ℝ) - Real.log (delta m : ℝ) = 2 * Real.log (3 * (m : ℝ) / 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : (delta m : ℝ) = 2 / (3 * (m : ℝ)^2) := by norm_num [delta]
  constructor
  · have heq : (m : ℝ) * (delta m : ℝ) = (3 * (m : ℝ) / 2)⁻¹ := by
      rw [hd]
      field_simp
    rw [heq, Real.log_inv]
    ring
  · rw [← Real.log_div (by norm_num : (3 / 2 : ℝ) ≠ 0)
      (by exact_mod_cast ne_of_gt (delta_pos hm))]
    have heq : (3 / 2 : ℝ) / (delta m : ℝ) = (3 * (m : ℝ) / 2)^2 := by
      rw [hd]
      field_simp
    rw [heq, Real.log_pow]
    norm_num

/-- Every recorded resource load is bounded by the directly proved 0/1 estimate. -/
lemma solve_load_bound {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (i : Fin m) :
    (value (solve c oracle).loads i : ℝ) ≤
      6 * Real.log (3 * (m : ℝ) / 2) * (value c i : ℝ) := by
  have hs : BasicInvariant c columns (solve c oracle) := run_invariant c columns oracle hm hc ho (fuel m)
  have ha : AnalyticInvariant c (solve c oracle) := run_analytic c columns oracle hm hc ho (fuel m)
  have hx : (0 : ℝ) < (value c i * value (solve c oracle).weights i : ℚ) := by
    exact_mod_cast mul_pos (hc i) (hs.positive i)
  have hu : ((value c i * value (solve c oracle).weights i : ℚ) : ℝ) ≤ 3 / 2 := by
    have hh : ((value c i * value (solve c oracle).weights i : ℚ) : ℝ) ≤ ((3/2 : ℚ) : ℝ) := by
      exact_mod_cast (hs.scaled_lt i).le
    norm_num at hh ⊢
    exact hh
  have hl := Real.log_le_log hx hu
  have hmul := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hl (Real.log (delta m : ℝ)))
    (show 0 ≤ 3 * (value c i : ℝ) by exact_mod_cast (mul_pos (by norm_num : (0 : ℚ) < 3) (hc i)).le)
  rw [(log_parameters hm).2] at hmul
  have h := (ha.load i).trans hmul
  nlinarith

/-- Real comparators are interpreted semantically and never stored in runtime data. -/
def RealFeasible {m : ℕ} (columns : Set (Column m)) (w : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∀ p ∈ columns, 1 ≤ ∑ i ∈ p, w i

lemma run_real_weak_duality {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (w : Fin m → ℝ) (hw : RealFeasible columns w)
    (n : ℕ) :
    ((run c oracle n).total : ℝ) ≤ ∑ i, (value (run c oracle n).loads i : ℝ) * w i := by
  induction n with
  | zero => simp [run, start]
  | succ n ih =>
    have hs := run_invariant c columns oracle hm hc ho n
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih
    · have hcast (i : Fin m) :
          ((if i ∈ (oracle (run c oracle n).weights).column then
            value c (oracle (run c oracle n).weights).bottleneck else 0 : ℚ) : ℝ) =
          if i ∈ (oracle (run c oracle n).weights).column then
            (value c (oracle (run c oracle n).weights).bottleneck : ℝ) else 0 := by
        split_ifs <;> simp
      simp only [run, step, ite_eq_right hstop, value_ofFn, Rat.cast_add, hcast,
        add_mul, Finset.sum_add_distrib]
      have hp := hw.2 _ (ho.chosen_mem _ hs.positive)
      have hb := mul_le_mul_of_nonneg_left hp
        (show 0 ≤ (value c (oracle (run c oracle n).weights).bottleneck : ℝ) by
          exact_mod_cast (hc _).le)
      have heq : (∑ i : Fin m,
          (if i ∈ (oracle (run c oracle n).weights).column then
            (value c (oracle (run c oracle n).weights).bottleneck : ℝ) else 0) * w i) =
          (value c (oracle (run c oracle n).weights).bottleneck : ℝ) *
            ∑ i ∈ (oracle (run c oracle n).weights).column, w i := by
        simp [Finset.mul_sum, ite_mul]
      rw [heq]
      linarith

/-- The retained rational covering is within factor three of ANY feasible real
covering, without asking for or constructing an optimum. -/
theorem solve_three_approximation_real {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (w : Fin m → ℝ) (hw : RealFeasible columns w) :
    (objective c (solve c oracle).best : ℝ) ≤ 3 * ∑ i, (value c i : ℝ) * w i := by
  have hs : BasicInvariant c columns (solve c oracle) := run_invariant c columns oracle hm hc ho (fuel m)
  have ha : AnalyticInvariant c (solve c oracle) := run_analytic c columns oracle hm hc ho (fuel m)
  have hz : (0 : ℝ) < (solve c oracle).bestCost := by exact_mod_cast hs.cost_pos
  have hp := ha.potential _ hz le_rfl
  have hstop : (1 : ℝ) ≤ (objective c (solve c oracle).weights : ℝ) := by
    exact_mod_cast solve_stopped c columns oracle hm hc ho
  have hlog : 0 ≤ Real.log (objective c (solve c oracle).weights : ℝ) :=
    Real.log_nonneg hstop
  have hinit : Real.log (objective c (initial c) : ℝ) =
      -Real.log (3 * (m : ℝ) / 2) := by
    rw [objective_initial c hc]
    push_cast
    linarith [(log_parameters hm).1]
  rw [hinit] at hp
  have hlower : 2 * (solve c oracle).bestCost * Real.log (3 * (m : ℝ) / 2) ≤
      ((solve c oracle).total : ℝ) := by nlinarith
  have hwk : ((solve c oracle).total : ℝ) ≤
      ∑ i, (value (solve c oracle).loads i : ℝ) * w i :=
    run_real_weak_duality c columns oracle hm hc ho w hw (fuel m)
  have hu : (∑ i, (value (solve c oracle).loads i : ℝ) * w i) ≤
      6 * Real.log (3 * (m : ℝ) / 2) * (∑ i, (value c i : ℝ) * w i) := by
    calc
      _ ≤ ∑ i, (6 * Real.log (3 * (m : ℝ) / 2) * (value c i : ℝ)) * w i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (solve_load_bound c columns oracle hm hc ho i) (hw.1 i)
      _ = _ := by simp [Finset.mul_sum, mul_assoc]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK : 0 < Real.log (3 * (m : ℝ) / 2) := Real.log_pos (by linarith)
  have hfinal : ((solve c oracle).bestCost : ℝ) ≤ 3 * ∑ i, (value c i : ℝ) * w i := by
    nlinarith [hwk.trans hu]
  rwa [hs.cost_eq] at hfinal

/-- Rational comparator specialization. -/
theorem solve_three_approximation {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (w : Row m) (hw : Feasible columns w) :
    objective c (solve c oracle).best ≤ 3 * objective c w := by
  have hwR : RealFeasible columns (fun i => (value w i : ℝ)) := by
    constructor
    · intro i
      change (0 : ℝ) ≤ (value w i : ℝ)
      exact_mod_cast hw.1 i
    · intro p hp
      change (1 : ℝ) ≤ ∑ i ∈ p, (value w i : ℝ)
      have hh := hw.2 p hp
      unfold length at hh
      exact_mod_cast hh
  have h := solve_three_approximation_real c columns oracle hm hc ho _ hwR
  exact_mod_cast h

end DirectedFlowCutGap.FractionalCover
