import DirectedFlowCutGap.MultiplicityCover
import DirectedFlowCutGap.FractionalCoverAnalysis

/-! The multiplicity-aware iteration charges each resource for its actual
coefficient times the selected amount. The analytical argument uses the
same one-step inequalities as the subset covering solver. -/
namespace DirectedFlowCutGap.MultiplicityCover

open scoped BigOperators
open FractionalCover (Row value value_ofFn objective delta initial fuel)

structure Analytical {m : ℕ} (c : Row m) (s : State m) : Prop where
  potential : ∀ z : ℝ, 0 < z → z ≤ (s.bestCost : ℝ) →
    2 * z * (Real.log (objective c s.weights : ℝ) -
      Real.log (objective c (initial c) : ℝ)) ≤ (s.total : ℝ)
  load : ∀ i, (value s.loads i : ℝ) ≤ 3 * (value c i : ℝ) *
    (Real.log (value c i * value s.weights i : ℚ) - Real.log (delta m : ℝ))

private theorem start_analytical {m : ℕ} (c : Row m) (oracle : Oracle m)
    (positive : ∀ i, 0 < value c i) : Analytical c (start c oracle) := by
  constructor
  · intro z _ _
    simp [start]
  · intro i
    simp [start, FractionalCover.initial_scaled c positive]

private theorem step_analytical {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (dim : 0 < m) (positive : ∀ i, 0 < value c i)
    (good : OracleCorrect c columns oracle) {s : State m}
    (valid : Invariant c columns s) (prior : Analytical c s) :
    Analytical c (step c oracle s) := by
  unfold step
  split
  · exact prior
  next _ =>
    let q := oracle s.weights
    have qpos := amount_pos c q positive (good.pivot _ valid.positive)
    have len := length_pos s.weights q.column valid.positive q.pivot (good.pivot _ valid.positive)
    have obj := FractionalCover.objective_pos c _ dim positive valid.positive
    constructor
    · intro z zpos best
      change z ≤ (min (objective c (normalized s.weights q.column)) s.bestCost : ℚ) at best
      have old : z ≤ (s.bestCost : ℝ) := best.trans (by exact_mod_cast min_le_right _ _)
      have current : z ≤ (objective c s.weights : ℝ) / (length s.weights q.column : ℝ) := by
        have chosen : z ≤ (objective c (normalized s.weights q.column) : ℝ) :=
          best.trans (by exact_mod_cast min_le_left _ _)
        rw [objective_normalized] at chosen
        exact_mod_cast chosen
      have gain := FractionalCover.potential_step (by exact_mod_cast obj) (by exact_mod_cast len)
        (show 0 ≤ (amount c q : ℝ) by exact_mod_cast qpos.le) zpos current
      have raised : (objective c (update c s.weights q) : ℝ) =
          (objective c s.weights : ℝ) + (amount c q : ℝ) * (length s.weights q.column : ℝ) / 2 := by
        have law := objective_update c s.weights q positive
        have lifted := congrArg (fun r : ℚ => (r : ℝ)) law
        convert lifted using 1
        push_cast
        ring
      change 2 * z * (Real.log (objective c (update c s.weights q) : ℝ) -
        Real.log (objective c (initial c) : ℝ)) ≤ ((s.total + amount c q : ℚ) : ℝ)
      rw [raised, Rat.cast_add]
      linarith [prior.potential z zpos old]
    · intro i
      have hc : (0 : ℝ) < value c i := by exact_mod_cast positive i
      have hx : (0 : ℝ) < (value c i * value s.weights i : ℚ) := by
        exact_mod_cast mul_pos (positive i) (valid.positive i)
      have hdeposit : (0 : ℝ) ≤ deposit c q i := by
        exact_mod_cast mul_nonneg qpos.le (show (0 : ℚ) ≤ coeff q.column i by positivity)
      have limit : (deposit c q i : ℝ) ≤ (value c i : ℝ) := by
        exact_mod_cast deposit_le c s.weights columns oracle good valid.positive positive i
      have paid := FractionalCover.load_step hc hx hdeposit limit
      have updated : ((value c i * value (update c s.weights q) i : ℚ) : ℝ) =
          ((value c i * value s.weights i : ℚ) : ℝ) * (1 + (deposit c q i : ℝ)/(2*(value c i : ℝ))) := by
        simp only [update, value_ofFn]
        push_cast
        ring
      change ((value (Vector.ofFn fun j => value s.loads j + deposit c q j) i : ℚ) : ℝ) ≤
        3 * (value c i : ℝ) * (Real.log (value c i * value (update c s.weights q) i : ℚ) -
          Real.log (delta m : ℝ))
      simp only [value_ofFn, Rat.cast_add, updated]
      linarith [prior.load i]

theorem run_analytical {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (dim : 0 < m) (positive : ∀ i, 0 < value c i)
    (good : OracleCorrect c columns oracle) (steps : ℕ) :
    Analytical c (run c oracle steps) := by
  induction steps with
  | zero => exact start_analytical c oracle positive
  | succ k ih =>
    exact step_analytical c columns oracle dim positive good
      (run_invariant c columns oracle dim positive good k) ih

theorem solve_load_le {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (dim : 0 < m) (positive : ∀ i, 0 < value c i)
    (good : OracleCorrect c columns oracle) (i : Fin m) :
    (value (solve c oracle).loads i : ℝ) ≤
      6 * Real.log (3 * (m : ℝ) / 2) * (value c i : ℝ) := by
  have valid : Invariant c columns (solve c oracle) :=
    run_invariant c columns oracle dim positive good (fuel m)
  have work : Analytical c (solve c oracle) :=
    run_analytical c columns oracle dim positive good (fuel m)
  have hx : (0 : ℝ) < (value c i * value (solve c oracle).weights i : ℚ) := by
    exact_mod_cast mul_pos (positive i) (valid.positive i)
  have hu : ((value c i * value (solve c oracle).weights i : ℚ) : ℝ) ≤ 3/2 := by
    have lift : ((value c i * value (solve c oracle).weights i : ℚ) : ℝ) ≤ ((3/2 : ℚ) : ℝ) := by
      exact_mod_cast (valid.scaled_lt i).le
    norm_num at lift ⊢
    exact lift
  have log := Real.log_le_log hx hu
  have hc : (0 : ℝ) < value c i := by exact_mod_cast positive i
  have mul := mul_le_mul_of_nonneg_left (sub_le_sub_right log (Real.log (delta m : ℝ)))
    (show 0 ≤ 3 * (value c i : ℝ) by positivity)
  rw [(FractionalCover.log_parameters dim).2] at mul
  exact ((work.load i).trans mul).trans_eq (by ring)

def RealFeasible {m : ℕ} (columns : Set (Column m)) (w : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∀ q ∈ columns, 1 ≤ ∑ i, (coeff q i : ℝ) * w i

theorem run_real_weak_duality {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (dim : 0 < m) (positive : ∀ i, 0 < value c i)
    (good : OracleCorrect c columns oracle) (w : Fin m → ℝ) (cover : RealFeasible columns w)
    (steps : ℕ) :
    ((run c oracle steps).total : ℝ) ≤ ∑ i, (value (run c oracle steps).loads i : ℝ) * w i := by
  induction steps with
  | zero => simp [run, start]
  | succ k ih =>
    let s := run c oracle k
    let q := oracle s.weights
    have valid := run_invariant c columns oracle dim positive good k
    change ((step c oracle s).total : ℝ) ≤ ∑ i, (value (step c oracle s).loads i : ℝ) * w i
    change (s.total : ℝ) ≤ ∑ i, (value s.loads i : ℝ) * w i at ih
    by_cases finished : 1 ≤ objective c s.weights
    · simpa only [step, ite_eq_left finished] using ih
    · have lower := cover.2 q.column (good.member _ valid.positive)
      have amountNonneg : (0 : ℝ) ≤ amount c q := by
        exact_mod_cast (amount_pos c q positive (good.pivot _ valid.positive)).le
      have raised := mul_le_mul_of_nonneg_left lower amountNonneg
      have each : (∑ i, (deposit c q i : ℝ) * w i) = (amount c q : ℝ) * ∑ i, (coeff q.column i : ℝ) * w i := by
        simp only [deposit, Rat.cast_mul, Rat.cast_natCast, Finset.mul_sum, mul_assoc]
      simp only [step, ite_eq_right finished, value_ofFn, Rat.cast_add, add_mul, Finset.sum_add_distrib]
      change (s.total : ℝ) + (amount c q : ℝ) ≤
        (∑ i, (value s.loads i : ℝ) * w i) + ∑ i, (deposit c q i : ℝ) * w i
      rw [each]
      linarith only [ih, raised]

/-- The computed covering is within three of every real feasible comparator. -/
theorem solve_three_approximation_real {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (dim : 0 < m) (positive : ∀ i, 0 < value c i)
    (good : OracleCorrect c columns oracle) (w : Fin m → ℝ) (cover : RealFeasible columns w) :
    (objective c (solve c oracle).best : ℝ) ≤ 3 * ∑ i, (value c i : ℝ) * w i := by
  let s := solve c oracle
  have valid : Invariant c columns s := run_invariant c columns oracle dim positive good (fuel m)
  have work : Analytical c s := run_analytical c columns oracle dim positive good (fuel m)
  have hz : (0 : ℝ) < s.bestCost := by exact_mod_cast valid.cost_pos
  have potential := work.potential _ hz le_rfl
  have reached : (1 : ℝ) ≤ (objective c s.weights : ℝ) := by exact_mod_cast solve_stopped c columns oracle dim positive good
  have hlog : 0 ≤ Real.log (objective c s.weights : ℝ) := Real.log_nonneg reached
  have init : Real.log (objective c (initial c) : ℝ) = -Real.log (3 * (m : ℝ) / 2) := by
    rw [FractionalCover.objective_initial c positive]
    push_cast
    linarith [(FractionalCover.log_parameters dim).1]
  rw [init] at potential
  have lower : 2 * (s.bestCost : ℝ) * Real.log (3 * (m : ℝ) / 2) ≤ (s.total : ℝ) := by
    apply le_trans _ potential
    exact mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by positivity)
  have weak : (s.total : ℝ) ≤ ∑ i, (value s.loads i : ℝ) * w i :=
    run_real_weak_duality c columns oracle dim positive good w cover (fuel m)
  have upper : (∑ i, (value s.loads i : ℝ) * w i) ≤
      6 * Real.log (3 * (m : ℝ) / 2) * ∑ i, (value c i : ℝ) * w i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (solve_load_le c columns oracle dim positive good i) (cover.1 i)
  have count : (1 : ℝ) ≤ m := by exact_mod_cast dim
  have gain : 0 < Real.log (3 * (m : ℝ) / 2) := Real.log_pos (by linarith)
  have compare : ((s.bestCost : ℚ) : ℝ) ≤ 3 * ∑ i, (value c i : ℝ) * w i := by
    apply le_of_mul_le_mul_left _ (show 0 < 2 * Real.log (3 * (m : ℝ) / 2) by positivity)
    calc
      _ = 2 * (s.bestCost : ℝ) * Real.log (3 * (m : ℝ) / 2) := by ring
      _ ≤ 6 * Real.log (3 * (m : ℝ) / 2) * ∑ i, (value c i : ℝ) * w i :=
        lower.trans (weak.trans upper)
      _ = _ := by ring
  rwa [valid.cost_eq] at compare

end DirectedFlowCutGap.MultiplicityCover
