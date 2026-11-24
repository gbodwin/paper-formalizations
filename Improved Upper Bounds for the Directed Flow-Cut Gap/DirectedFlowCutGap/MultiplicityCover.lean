import DirectedFlowCutGap.FractionalCoverAnalysis

/-! Packing updates for covering columns with integer multiplicities. A
column can be the sum of one path incidence vector per demand. -/
namespace DirectedFlowCutGap.MultiplicityCover

open scoped BigOperators
open FractionalCover (Row value objective delta initial fuel)

abbrev Column (m : ℕ) := Vector ℕ m

def coeff {m : ℕ} (column : Column m) (i : Fin m) : ℕ := column[i.val]

def length {m : ℕ} (y : Row m) (column : Column m) : ℚ :=
  ∑ i, (coeff column i : ℚ)*value y i

structure Choice (m : ℕ) where
  column : Column m
  pivot : Fin m

abbrev Oracle (m : ℕ) := Row m → Choice m

structure OracleCorrect {m : ℕ} (c : Row m) (columns : Set (Column m)) (oracle : Oracle m) : Prop where
  member : ∀ y, (∀ i, 0 < value y i) → (oracle y).column∈columns
  pivot : ∀ y, (∀ i, 0 < value y i) → 0 < coeff (oracle y).column (oracle y).pivot
  bottleneck : ∀ y, (∀ i, 0 < value y i) → ∀ i, 0 < coeff (oracle y).column i →
    value c (oracle y).pivot / (coeff (oracle y).column (oracle y).pivot : ℚ) ≤
      value c i/(coeff (oracle y).column i : ℚ)
  shortest : ∀ y, (∀ i, 0 < value y i) → ∀ p∈columns, length y (oracle y).column≤length y p

def amount {m : ℕ} (c : Row m) (choice : Choice m) : ℚ :=
  value c choice.pivot/(coeff choice.column choice.pivot : ℚ)

def deposit {m : ℕ} (c : Row m) (choice : Choice m) (i : Fin m) : ℚ :=
  amount c choice*(coeff choice.column i : ℚ)

theorem amount_pos {m : ℕ} (c : Row m) (choice : Choice m)
    (cpos : ∀ i, 0 < value c i) (pivot : 0 < coeff choice.column choice.pivot) :
    0 < amount c choice := div_pos (cpos _) (by exact_mod_cast pivot)

theorem deposit_pivot {m : ℕ} (c : Row m) (choice : Choice m) (pivot : 0 < coeff choice.column choice.pivot) :
    deposit c choice choice.pivot=value c choice.pivot := by
  unfold deposit amount
  have nz : (coeff choice.column choice.pivot : ℚ)≠0 := by exact_mod_cast pivot.ne'
  exact div_mul_cancel₀ _ nz

theorem deposit_le {m : ℕ} (c y : Row m) (columns : Set (Column m)) (oracle : Oracle m)
    (good : OracleCorrect c columns oracle) (weights : ∀ i, 0 < value y i) (cpos : ∀ i, 0 < value c i)
    (i : Fin m) : deposit c (oracle y) i ≤ value c i := by
  obtain zero | positive := Nat.eq_zero_or_pos (coeff (oracle y).column i)
  · unfold deposit
    rw [zero,Nat.cast_zero,mul_zero]
    exact (cpos i).le
  · exact (le_div_iff₀ (by exact_mod_cast positive)).mp (good.bottleneck y weights i positive)

theorem length_pos {m : ℕ} (y : Row m) (p : Column m) (weights : ∀ i, 0 < value y i)
    (pivot : Fin m) (present : 0 < coeff p pivot) : 0 < length y p := by
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (by positivity) (weights i).le
  · exact ⟨pivot,Finset.mem_univ _,mul_pos (by exact_mod_cast present) (weights pivot)⟩

def normalized {m : ℕ} (y : Row m) (p : Column m) : Row m :=
  Vector.ofFn fun i => value y i/length y p

def Feasible {m : ℕ} (columns : Set (Column m)) (w : Row m) : Prop :=
  (∀ i, 0≤value w i) ∧ ∀ p∈columns, 1≤length w p

theorem normalized_feasible {m : ℕ} (c y : Row m) (columns : Set (Column m)) (oracle : Oracle m)
    (good : OracleCorrect c columns oracle) (positive : ∀ i, 0 < value y i) :
    Feasible columns (normalized y (oracle y).column) := by
  have scale := length_pos y (oracle y).column positive _ (good.pivot y positive)
  constructor
  · intro i
    simp only [normalized,FractionalCover.value_ofFn]
    exact div_nonneg (positive i).le scale.le
  · intro p valid
    simp only [length, normalized, FractionalCover.value_ofFn, ← mul_div_assoc, ← Finset.sum_div]
    exact (le_div_iff₀ scale).mpr (by
      simpa only [one_mul, length] using good.shortest y positive p valid)

theorem objective_normalized {m : ℕ} (c y : Row m) (p : Column m) :
    objective c (normalized y p)=objective c y/length y p := by
  simp only [objective, normalized, FractionalCover.value_ofFn, ← mul_div_assoc, ← Finset.sum_div]

def update {m : ℕ} (c y : Row m) (choice : Choice m) : Row m :=
  Vector.ofFn fun i => value y i*(1+deposit c choice i/(2*value c i))

theorem objective_update {m : ℕ} (c y : Row m) (choice : Choice m) (positive : ∀ i, 0 < value c i) :
    objective c (update c y choice)=objective c y+(amount c choice/2)*length y choice.column := by
  unfold objective length
  simp only [update,FractionalCover.value_ofFn,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold deposit
  field_simp [(positive i).ne']

structure State (m : ℕ) where
  weights : Row m
  best : Row m
  bestCost : ℚ
  total : ℚ
  loads : Row m

def start {m : ℕ} (c : Row m) (oracle : Oracle m) : State m :=
  let y := initial c
  let w := normalized y (oracle y).column
  ⟨y,w,objective c w,0,Vector.replicate m 0⟩

def step {m : ℕ} (c : Row m) (oracle : Oracle m) (s : State m) : State m :=
  if 1≤objective c s.weights then s else
    let pick := oracle s.weights
    let w := normalized s.weights pick.column
    let fee := objective c w
    ⟨update c s.weights pick, if fee < s.bestCost then w else s.best, min fee s.bestCost,
      s.total+amount c pick, Vector.ofFn fun i => value s.loads i+deposit c pick i⟩

def run {m : ℕ} (c : Row m) (oracle : Oracle m) : ℕ → State m
  | 0 => start c oracle
  | n+1 => step c oracle (run c oracle n)

def solve {m : ℕ} (c : Row m) (oracle : Oracle m) : State m := run c oracle (fuel m)

structure Invariant {m : ℕ} (c : Row m) (columns : Set (Column m)) (state : State m) : Prop where
  positive : ∀ i, 0 < value state.weights i
  initial_le : ∀ i, delta m≤value c i*value state.weights i
  scaled_lt : ∀ i, value c i*value state.weights i<3/2
  feasible : Feasible columns state.best
  cost_eq : state.bestCost=objective c state.best
  cost_pos : 0<state.bestCost

private theorem initial_valid {m : ℕ} (c : Row m) (columns : Set (Column m)) (oracle : Oracle m)
    (dim : 0 < m) (cpos : ∀ i, 0 < value c i) (good : OracleCorrect c columns oracle) :
    Invariant c columns (start c oracle) := by
  have positive := FractionalCover.initial_pos c dim cpos
  refine ⟨positive,?_,?_,normalized_feasible c _ columns oracle good positive,rfl,?_⟩
  · intro i
    exact (FractionalCover.initial_scaled c cpos i).ge
  · intro i
    change value c i*value (initial c) i < 3/2
    rw [FractionalCover.initial_scaled c cpos i]
    linarith only [FractionalCover.delta_le dim]
  · change 0<objective c (normalized (initial c) (oracle (initial c)).column)
    rw [objective_normalized]
    exact div_pos (FractionalCover.objective_pos c _ dim cpos positive)
      (length_pos _ _ positive _ (good.pivot _ positive))

private theorem next_valid {m : ℕ} (c : Row m) (columns : Set (Column m)) (oracle : Oracle m)
    (dim : 0 < m) (cpos : ∀ i, 0 < value c i) (good : OracleCorrect c columns oracle)
    {s : State m} (inv : Invariant c columns s) : Invariant c columns (step c oracle s) := by
  unfold step
  split
  · exact inv
  next unfinished =>
    let q := oracle s.weights
    let w := normalized s.weights q.column
    have qpositive := amount_pos c q cpos (good.pivot _ inv.positive)
    have wfeasible := normalized_feasible c s.weights columns oracle good inv.positive
    have score : 0<objective c w := by
      unfold w
      rw [objective_normalized]
      exact div_pos (FractionalCover.objective_pos c _ dim cpos inv.positive)
        (length_pos _ _ inv.positive _ (good.pivot _ inv.positive))
    have bNonneg (i : Fin m) : 0≤deposit c q i := mul_nonneg qpositive.le (by positivity)
    have ratio (i : Fin m) : 0≤deposit c q i/(2*value c i) :=
      div_nonneg (bNonneg i) (by positivity [cpos i])
    have charges (i : Fin m) : deposit c q i/(2*value c i) ≤ 1/2 := by
      have cap := deposit_le c s.weights columns oracle good inv.positive cpos i
      apply (div_le_iff₀ (show 0<2*value c i by positivity [cpos i])).mpr
      linarith only [cap]
    refine ⟨?_,?_,?_,?_,?_,lt_min score inv.cost_pos⟩
    · intro i
      simp only [update,FractionalCover.value_ofFn]
      exact mul_pos (inv.positive i) (by linarith only [ratio i])
    · intro i
      simp only [update,FractionalCover.value_ofFn]
      rw [← mul_assoc]
      exact (inv.initial_le i).trans (le_mul_of_one_le_right (by positivity [cpos i,inv.positive i])
        (by linarith only [ratio i]))
    · intro i
      have single : value c i*value s.weights i≤objective c s.weights :=
        Finset.single_le_sum (fun j _ => mul_nonneg (cpos j).le (inv.positive j).le) (Finset.mem_univ i)
      have pre : value c i*value s.weights i<1 := single.trans_lt (lt_of_not_ge unfinished)
      have factor : 1+deposit c q i/(2*value c i)≤3/2 := by linarith only [charges i]
      simp only [update,FractionalCover.value_ofFn,←mul_assoc]
      calc
        _ ≤ (value c i*value s.weights i)*(3/2) :=
          mul_le_mul_of_nonneg_left factor (mul_nonneg (cpos i).le (inv.positive i).le)
        _ < _ := by linarith only [pre]
    · change Feasible columns (if objective c w < s.bestCost then w else s.best)
      split
      · exact wfeasible
      · exact inv.feasible
    · change min (objective c w) s.bestCost =
        objective c (if objective c w < s.bestCost then w else s.best)
      split
      next improved => exact min_eq_left improved.le
      next kept => exact (min_eq_right (le_of_not_gt kept)).trans inv.cost_eq

theorem run_invariant {m : ℕ} (c : Row m) (columns : Set (Column m)) (oracle : Oracle m)
    (dim : 0 < m) (cpos : ∀ i, 0 < value c i) (good : OracleCorrect c columns oracle) (steps : ℕ) :
    Invariant c columns (run c oracle steps) := by
  induction steps with
  | zero => exact initial_valid c columns oracle dim cpos good
  | succ k ih => exact next_valid c columns oracle dim cpos good ih

private theorem increment {m : ℕ} (c y : Row m) (choice : Choice m)
    (positive : ∀ i, 0 < value c i) (row : ∀ i, 0 < value y i)
    (pivot : 0 < coeff choice.column choice.pivot) (lower : ∀ i, delta m≤value c i*value y i) :
    objective c y+delta m/2≤objective c (update c y choice) := by
  have vp : (coeff choice.column choice.pivot : ℚ)*value y choice.pivot≤length y choice.column :=
    Finset.single_le_sum (fun i _ => mul_nonneg (by positivity) (row i).le) (Finset.mem_univ _)
  have paid := mul_le_mul_of_nonneg_left vp ((amount_pos c choice positive pivot).le)
  rw [←mul_assoc,←deposit,deposit_pivot c choice pivot] at paid
  rw [objective_update c y choice positive]
  linarith only [paid,lower choice.pivot]

theorem solve_stopped {m : ℕ} (c : Row m) (columns : Set (Column m)) (oracle : Oracle m)
    (dim : 0 < m) (positive : ∀ i, 0 < value c i) (good : OracleCorrect c columns oracle) :
    1≤objective c (solve c oracle).weights := by
  have after (n : ℕ) : 1≤objective c (run c oracle n).weights ∨
      objective c (initial c)+(n : ℚ)*(delta m/2)≤objective c (run c oracle n).weights := by
    induction n with
    | zero => right; simp [run,start]
    | succ n ih =>
      by_cases stopped : 1≤objective c (run c oracle n).weights
      · left; simpa only [run,step,ite_eq_left stopped] using stopped
      · have previous := ih.resolve_left stopped
        have valid := run_invariant c columns oracle dim positive good n
        have increase := increment c _ (oracle _) positive valid.positive
          (good.pivot _ valid.positive) valid.initial_le
        right
        simp only [run,step,ite_eq_right stopped]
        push_cast
        linarith only [previous,increase]
  rcases after (fuel m) with h | h
  · exact h
  · have enough : (fuel m : ℚ)*(delta m/2)=1 := by
      unfold fuel delta
      push_cast
      field_simp [ne_of_gt (show (0 : ℚ)<m by exact_mod_cast dim)]
    rw [enough] at h
    exact (le_add_of_nonneg_left (FractionalCover.objective_pos c _ dim positive
      (FractionalCover.initial_pos c dim positive)).le).trans h

end DirectedFlowCutGap.MultiplicityCover
