import Mathlib

/-!
# Executable positive-cost rational 0/1 covering recurrence

The minimum-column oracle is supplied as executable data; its semantic contract
is a separate proposition. No finite column family is enumerated by this code.
All stored weights, objectives and amounts are rational. Graph shortest-path
witness extraction and bit-operation bounds are separate obligations.
-/
namespace DirectedFlowCutGap.FractionalCover
open scoped BigOperators

abbrev Row (m : ℕ) := Vector ℚ m
abbrev Column (m : ℕ) := Finset (Fin m)

def value {m : ℕ} (x : Row m) (i : Fin m) : ℚ := x[i.val]
def objective {m : ℕ} (c y : Row m) : ℚ := ∑ i, value c i * value y i
def length {m : ℕ} (y : Row m) (p : Column m) : ℚ := ∑ i ∈ p, value y i

/-- An actual column together with an attained bottleneck index. -/
structure Choice (m : ℕ) where
  column : Column m
  bottleneck : Fin m

abbrev Oracle (m : ℕ) := Row m → Choice m

/-- Only proof fields depend on the semantic family of columns. -/
structure OracleCorrect {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) : Prop where
  chosen_mem : ∀ y, (∀ i, 0 < value y i) → (oracle y).column ∈ columns
  bottleneck_mem : ∀ y, (∀ i, 0 < value y i) →
    (oracle y).bottleneck ∈ (oracle y).column
  bottleneck_min : ∀ y, (∀ i, 0 < value y i) → ∀ i ∈ (oracle y).column,
    value c (oracle y).bottleneck ≤ value c i
  minimum : ∀ y, (∀ i, 0 < value y i) → ∀ p ∈ columns,
    length y (oracle y).column ≤ length y p

def Feasible {m : ℕ} (columns : Set (Column m)) (w : Row m) : Prop :=
  (∀ i, 0 ≤ value w i) ∧ ∀ p ∈ columns, 1 ≤ length w p

def delta (m : ℕ) : ℚ := 2 / (3 * (m : ℚ)^2)
def initial {m : ℕ} (c : Row m) : Row m :=
  Vector.ofFn fun i => delta m / value c i

def normalized {m : ℕ} (y : Row m) (p : Column m) : Row m :=
  Vector.ofFn fun i => value y i / length y p

def update {m : ℕ} (c y : Row m) (q : Choice m) : Row m :=
  Vector.ofFn fun i => if i ∈ q.column then
    value y i * (1 + value c q.bottleneck / (2 * value c i)) else value y i

/-- The trace records exactly the updates that actually took place. -/
structure Event (m : ℕ) where
  choice : Choice m
  amount : ℚ

structure State (m : ℕ) where
  weights : Row m
  best : Row m
  bestCost : ℚ
  total : ℚ
  loads : Row m
  events : List (Event m)

def start {m : ℕ} (c : Row m) (oracle : Oracle m) : State m :=
  let y := initial c
  let w := normalized y (oracle y).column
  { weights := y, best := w, bestCost := objective c w,
    total := 0, loads := Vector.replicate m 0, events := [] }

/-- The stop test is rational, and a stopped state performs no more oracle calls. -/
def step {m : ℕ} (c : Row m) (oracle : Oracle m) (s : State m) : State m :=
  if 1 ≤ objective c s.weights then s else
    let q := oracle s.weights
    let b := value c q.bottleneck
    let w := normalized s.weights q.column
    let improve := objective c w < s.bestCost
    { weights := update c s.weights q
      best := if improve then w else s.best
      bestCost := min (objective c w) s.bestCost
      total := s.total + b
      loads := Vector.ofFn fun i => value s.loads i + if i ∈ q.column then b else 0
      events := { choice := q, amount := b } :: s.events }

def run {m : ℕ} (c : Row m) (oracle : Oracle m) : ℕ → State m
  | 0 => start c oracle
  | n + 1 => step c oracle (run c oracle n)

def fuel (m : ℕ) : ℕ := 3 * m^2

def solve {m : ℕ} (c : Row m) (oracle : Oracle m) : State m := run c oracle (fuel m)

@[simp] theorem value_ofFn {m : ℕ} (f : Fin m → ℚ) (i : Fin m) :
    value (Vector.ofFn f) i = f i := by simp [value]
@[simp] theorem value_replicate {m : ℕ} (q : ℚ) (i : Fin m) :
    value (Vector.replicate m q) i = q := by simp [value]

lemma delta_pos {m : ℕ} (hm : 0 < m) : 0 < delta m := by
  unfold delta
  positivity

lemma delta_le {m : ℕ} (hm : 0 < m) : delta m ≤ 2 / 3 := by
  have h : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hh : (1 : ℚ) ≤ (m : ℚ)^2 := by nlinarith
  unfold delta
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℚ) < 3)).2
  nlinarith

lemma initial_pos {m : ℕ} (c : Row m) (hm : 0 < m)
    (hc : ∀ i, 0 < value c i) : ∀ i, 0 < value (initial c) i := by
  intro i
  simpa [initial] using div_pos (delta_pos hm) (hc i)

lemma initial_scaled {m : ℕ} (c : Row m) (hc : ∀ i, 0 < value c i) (i : Fin m) :
    value c i * value (initial c) i = delta m := by
  simp only [initial, value_ofFn]
  field_simp [ne_of_gt (hc i)]

lemma objective_initial {m : ℕ} (c : Row m) (hc : ∀ i, 0 < value c i) :
    objective c (initial c) = m * delta m := by
  simp [objective, initial_scaled c hc]

lemma length_pos {m : ℕ} {y : Row m} (hy : ∀ i, 0 < value y i)
    {p : Column m} (hp : p.Nonempty) : 0 < length y p := by
  exact Finset.sum_pos (fun i _ => hy i) hp

lemma length_single_le {m : ℕ} {y : Row m} (hy : ∀ i, 0 ≤ value y i)
    {p : Column m} {i : Fin m} (hi : i ∈ p) : value y i ≤ length y p :=
  Finset.single_le_sum (fun j _ => hy j) hi

lemma objective_normalized {m : ℕ} (c y : Row m) (p : Column m) :
    objective c (normalized y p) = objective c y / length y p := by
  simp only [objective, normalized, value_ofFn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma normalized_feasible {m : ℕ} (c y : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (ho : OracleCorrect c columns oracle)
    (hy : ∀ i, 0 < value y i) : Feasible columns (normalized y (oracle y).column) := by
  have ha := length_pos hy ⟨_, ho.bottleneck_mem y hy⟩
  constructor
  · intro i
    simp only [normalized, value_ofFn]
    exact (div_pos (hy i) ha).le
  · intro p hp
    simp only [length, normalized, value_ofFn, ← Finset.sum_div]
    apply (le_div_iff₀ ha).2
    simpa only [one_mul, length] using ho.minimum y hy p hp

lemma update_pos {m : ℕ} (c y : Row m) (q : Choice m)
    (hc : ∀ i, 0 < value c i) (hy : ∀ i, 0 < value y i) :
    ∀ i, 0 < value (update c y q) i := by
  intro i
  simp only [update, value_ofFn]
  split_ifs
  · have hf := div_nonneg (hc q.bottleneck).le
      (mul_pos (by norm_num : (0 : ℚ) < 2) (hc i)).le
    exact mul_pos (hy i) (by linarith)
  · exact hy i

lemma update_mono {m : ℕ} (c y : Row m) (q : Choice m)
    (hc : ∀ i, 0 < value c i) (hy : ∀ i, 0 ≤ value y i) (i : Fin m) :
    value y i ≤ value (update c y q) i := by
  simp only [update, value_ofFn]
  split_ifs
  · have hf := div_nonneg (hc q.bottleneck).le (mul_pos (by norm_num : (0 : ℚ) < 2) (hc i)).le
    nlinarith [mul_nonneg (hy i) hf]
  · exact le_rfl

lemma objective_update {m : ℕ} (c y : Row m) (q : Choice m)
    (hc : ∀ i, 0 < value c i) :
    objective c (update c y q) = objective c y + value c q.bottleneck * length y q.column / 2 := by
  have h (i : Fin m) : value c i * value (update c y q) i =
      value c i * value y i + if i ∈ q.column then value c q.bottleneck * value y i / 2 else 0 := by
    simp only [update, value_ofFn]
    split_ifs
    · field_simp [ne_of_gt (hc i)]
    · ring
  simp only [objective, h, Finset.sum_add_distrib]
  congr 1
  simp [length, Finset.mul_sum, Finset.sum_div]

lemma objective_single_le {m : ℕ} (c y : Row m)
    (hc : ∀ i, 0 ≤ value c i) (hy : ∀ i, 0 ≤ value y i) (i : Fin m) :
    value c i * value y i ≤ objective c y :=
  Finset.single_le_sum (fun j _ => mul_nonneg (hc j) (hy j)) (Finset.mem_univ i)

lemma update_scaled_lt {m : ℕ} (c y : Row m) (q : Choice m)
    (hc : ∀ i, 0 < value c i) (hy : ∀ i, 0 < value y i)
    (hb : ∀ i ∈ q.column, value c q.bottleneck ≤ value c i)
    (hD : objective c y < 1) (i : Fin m) :
    value c i * value (update c y q) i < 3 / 2 := by
  have hs := (objective_single_le c y (fun i => (hc i).le) (fun i => (hy i).le) i).trans_lt hD
  simp only [update, value_ofFn]
  split_ifs with hi
  · have hf : value c q.bottleneck / (2 * value c i) ≤ 1 / 2 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) (hc i))).2
      linarith [hb i hi]
    have hscaled := mul_pos (hc i) (hy i)
    have hmul := mul_le_mul_of_nonneg_left hf hscaled.le
    nlinarith
  · linarith

lemma objective_increment {m : ℕ} (c y : Row m) (q : Choice m)
    (hc : ∀ i, 0 < value c i) (hy : ∀ i, 0 < value y i)
    (hb : q.bottleneck ∈ q.column)
    (hinit : ∀ i, delta m ≤ value c i * value y i) :
    objective c y + delta m / 2 ≤ objective c (update c y q) := by
  rw [objective_update c y q hc]
  have hs := mul_le_mul_of_nonneg_left
    (length_single_le (fun i => (hy i).le) hb) (hc q.bottleneck).le
  linarith [hinit q.bottleneck]

/-- The loop invariant uses only rational quantities; no logarithm is executed. -/
structure BasicInvariant {m : ℕ} (c : Row m) (columns : Set (Column m))
    (s : State m) : Prop where
  positive : ∀ i, 0 < value s.weights i
  initial_le : ∀ i, delta m ≤ value c i * value s.weights i
  scaled_lt : ∀ i, value c i * value s.weights i < 3 / 2
  feasible : Feasible columns s.best
  cost_eq : s.bestCost = objective c s.best
  cost_pos : 0 < s.bestCost
  total_nonneg : 0 ≤ s.total
  loads_nonneg : ∀ i, 0 ≤ value s.loads i

lemma objective_pos {m : ℕ} (c y : Row m) (hm : 0 < m)
    (hc : ∀ i, 0 < value c i) (hy : ∀ i, 0 < value y i) : 0 < objective c y := by
  apply Finset.sum_pos (fun i _ => mul_pos (hc i) (hy i))
  exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩

lemma start_invariant {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) : BasicInvariant c columns (start c oracle) := by
  have hy := initial_pos c hm hc
  have ha := length_pos hy ⟨_, ho.bottleneck_mem _ hy⟩
  refine ⟨hy, ?_, ?_, normalized_feasible c _ columns oracle ho hy, rfl, ?_, le_rfl, ?_⟩
  · intro i
    exact (initial_scaled c hc i).ge
  · intro i
    change value c i * value (initial c) i < 3 / 2
    rw [initial_scaled c hc]
    linarith [delta_le hm]
  · change 0 < objective c (normalized _ _)
    rw [objective_normalized]
    exact div_pos (objective_pos c _ hm hc hy) ha
  · intro i
    simp [start]

lemma step_invariant {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) {s : State m} (hs : BasicInvariant c columns s) :
    BasicInvariant c columns (step c oracle s) := by
  unfold step
  split_ifs with hstop
  · exact hs
  · have hy := hs.positive
    have ha := length_pos hy ⟨_, ho.bottleneck_mem _ hy⟩
    have hcost : 0 < objective c (normalized s.weights (oracle s.weights).column) := by
      rw [objective_normalized]
      exact div_pos (objective_pos c _ hm hc hy) ha
    refine ⟨update_pos c _ _ hc hy, ?_, ?_, ?_, ?_, lt_min hcost hs.cost_pos, ?_, ?_⟩
    · intro i
      exact (hs.initial_le i).trans (mul_le_mul_of_nonneg_left
        (update_mono c _ _ hc (fun i => (hy i).le) i) (hc i).le)
    · exact update_scaled_lt c _ _ hc hy (ho.bottleneck_min _ hy) (lt_of_not_ge hstop)
    · dsimp
      split_ifs
      · exact normalized_feasible c _ columns oracle ho hy
      · exact hs.feasible
    · dsimp
      split_ifs with himprove
      · exact min_eq_left himprove.le
      · rw [min_eq_right (le_of_not_gt himprove), hs.cost_eq]
    · exact add_nonneg hs.total_nonneg (hc _).le
    · intro i
      simp only [value_ofFn]
      split_ifs <;> linarith [hs.loads_nonneg i, hc (oracle s.weights).bottleneck]

lemma run_invariant {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (n : ℕ) :
    BasicInvariant c columns (run c oracle n) := by
  induction n with
  | zero => exact start_invariant c columns oracle hm hc ho
  | succ n ih => exact step_invariant c columns oracle hm hc ho ih

/-- If the loop has not stopped, every elapsed iteration increased the potential. -/
lemma run_progress {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (n : ℕ) :
    1 ≤ objective c (run c oracle n).weights ∨
      objective c (initial c) + n * (delta m / 2) ≤ objective c (run c oracle n).weights := by
  induction n with
  | zero => right; simp [run, start]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · left
      simp [run, step, hstop]
    · right
      have hp := ih.resolve_left hstop
      have hs := run_invariant c columns oracle hm hc ho n
      have hi := objective_increment c _ (oracle _) hc hs.positive
        (ho.bottleneck_mem _ hs.positive) hs.initial_le
      simp only [run, step, ite_eq_right hstop]
      push_cast
      linarith

/-- An explicit polynomial natural fuel always reaches the rational stop test. -/
theorem solve_stopped {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) : 1 ≤ objective c (solve c oracle).weights := by
  rcases run_progress c columns oracle hm hc ho (fuel m) with h | h
  · exact h
  · have hf : (fuel m : ℚ) * (delta m / 2) = 1 := by
      unfold fuel delta
      push_cast
      field_simp [ne_of_gt (show (0 : ℚ) < m by exact_mod_cast hm)]
    rw [hf] at h
    exact le_trans (by linarith [objective_pos c _ hm hc (initial_pos c hm hc)]) h

/-- The retained output is an actual rational feasible covering. -/
theorem solve_feasible {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) : Feasible columns (solve c oracle).best :=
  (run_invariant c columns oracle hm hc ho (fuel m)).feasible

lemma run_event_count {m : ℕ} (c : Row m) (oracle : Oracle m) (n : ℕ) :
    (run c oracle n).events.length ≤ n := by
  induction n with
  | zero => simp [run, start]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih.trans (Nat.le_succ n)
    · simpa only [run, step, ite_eq_right hstop, List.length_cons] using Nat.succ_le_succ ih

/-- Initialization uses one oracle call; each recorded update uses one more. -/
def oracleCalls {m : ℕ} (s : State m) : ℕ := s.events.length + 1

lemma solve_oracle_calls {m : ℕ} (c : Row m) (oracle : Oracle m) :
    oracleCalls (solve c oracle) ≤ 3 * m^2 + 1 := by
  exact Nat.add_le_add_right (run_event_count c oracle (fuel m)) 1

lemma step_bestCost_le {m : ℕ} (c : Row m) (oracle : Oracle m) (s : State m) :
    (step c oracle s).bestCost ≤ s.bestCost := by
  unfold step
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

lemma run_bestCost_antitone {m : ℕ} (c : Row m) (oracle : Oracle m) :
    Antitone (fun n => (run c oracle n).bestCost) := by
  apply antitone_nat_of_succ_le
  intro n
  exact step_bestCost_le c oracle _

/-- The retained cost is at most every pre-update ratio actually examined. -/
lemma run_best_le_updated {m : ℕ} (c : Row m) (oracle : Oracle m) {k n : ℕ}
    (hkn : k < n) (hk : objective c (run c oracle k).weights < 1) :
    (run c oracle n).bestCost ≤ objective c (run c oracle k).weights /
      length (run c oracle k).weights (oracle (run c oracle k).weights).column := by
  calc
    _ ≤ (run c oracle (k+1)).bestCost := run_bestCost_antitone c oracle hkn
    _ ≤ objective c (normalized (run c oracle k).weights
        (oracle (run c oracle k).weights).column) := by
      simp only [run, step, ite_eq_right (not_le.mpr hk)]
      exact min_le_left _ _
    _ = _ := objective_normalized _ _ _

/-- The output vector itself is retained from a visited normalization. -/
lemma run_best_attained {m : ℕ} (c : Row m) (oracle : Oracle m) (n : ℕ) :
    ∃ k ≤ n, (run c oracle n).best = normalized (run c oracle k).weights
      (oracle (run c oracle k).weights).column := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    change ∃ k ≤ n+1, (step c oracle (run c oracle n)).best =
      normalized (run c oracle k).weights (oracle (run c oracle k).weights).column
    simp only [step]
    split_ifs with hstop himprove
    · obtain ⟨k, hk, heq⟩ := ih
      exact ⟨k, hk.trans (Nat.le_succ _), heq⟩
    · exact ⟨n, Nat.le_succ _, rfl⟩
    · obtain ⟨k, hk, heq⟩ := ih
      exact ⟨k, hk.trans (Nat.le_succ _), heq⟩

/-- Finite weak duality is preserved by the actual recorded update amounts. -/
lemma run_weak_duality {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (w : Row m) (hw : Feasible columns w)
    (n : ℕ) :
    (run c oracle n).total ≤ ∑ i, value (run c oracle n).loads i * value w i := by
  induction n with
  | zero => simp [run, start]
  | succ n ih =>
    have hs := run_invariant c columns oracle hm hc ho n
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih
    · simp only [run, step, ite_eq_right hstop, value_ofFn, add_mul, Finset.sum_add_distrib]
      have hp := hw.2 _ (ho.chosen_mem _ hs.positive)
      have hb := mul_le_mul_of_nonneg_left hp (hc (oracle (run c oracle n).weights).bottleneck).le
      have heq : (∑ i : Fin m,
          (if i ∈ (oracle (run c oracle n).weights).column then
            value c (oracle (run c oracle n).weights).bottleneck else 0) * value w i) =
          value c (oracle (run c oracle n).weights).bottleneck *
            length w (oracle (run c oracle n).weights).column := by
        simp [length, Finset.mul_sum, ite_mul]
      rw [heq]
      linarith

end DirectedFlowCutGap.FractionalCover
