import DirectedFlowCutGap.FractionalCoverAnalysis
import DirectedFlowCutGap.RawNonnegativeRational

/-!
# Unreduced natural-fraction covering recurrence

This implementation never normalizes a rational. Runtime weights, objectives,
loads and amounts use the checked natural numerator/positive denominator code;
all comparisons are cross-products. The exact refinement relation to the frozen
rational recurrence is proof-only. An executable raw minimum-column oracle is
supplied separately. Natural arithmetic bit-operation realization is not
asserted by a bound on representation widths.
-/
namespace DirectedFlowCutGap.FractionalCoverRawCore
open scoped BigOperators NNRat
open FractionalCover RawNonnegativeRational
variable {m : ℕ}

abbrev RawRow (m : ℕ) := Vector Code m

def get (y : RawRow m) (i : Fin m) : Code := y[i.val]
def rational (q : Code) : ℚ := (q.value : ℚ)
def decodeRow (y : RawRow m) : FractionalCover.Row m := Vector.ofFn (fun i => rational (get y i))

@[simp] lemma get_ofFn (f : Fin m → Code) (i : Fin m) : get (Vector.ofFn f) i = f i := by
  simp [get]
@[simp] lemma decode_value (y : RawRow m) (i : Fin m) :
    value (decodeRow y) i = rational (get y i) := by simp [decodeRow]
@[simp] lemma rational_zero : rational Code.zero = 0 := by simp [rational]
@[simp] lemma rational_one : rational Code.one = 1 := by simp [rational]
@[simp] lemma rational_nat (n : ℕ) : rational (Code.ofNat n) = n := by simp [rational]
@[simp] lemma rational_add (a b : Code) : rational (a.add b) = rational a+rational b := by
  simp [rational]
@[simp] lemma rational_mul (a b : Code) : rational (a.mul b) = rational a*rational b := by
  simp [rational]
@[simp] lemma rational_div (a b : Code) : rational (a.div b) = rational a/rational b := by
  simp [rational]
@[simp] lemma code_le_iff (a b : Code) : a.le b = true ↔ rational a ≤ rational b := by
  rw [Code.le_eq_true]
  exact_mod_cast (Iff.rfl : a.value ≤ b.value ↔ a.value ≤ b.value)

lemma rational_nonneg (a : Code) : 0 ≤ rational a := a.value.property

def sumCodes : List Code → Code
  | [] => Code.zero
  | q::qs => q.add (sumCodes qs)

@[simp] lemma rational_sum (xs : List Code) :
    rational (sumCodes xs) = (xs.map rational).sum := by
  induction xs with
  | nil => simp [sumCodes]
  | cons x xs ih => simp [sumCodes,ih]

def objectiveCode (c y : RawRow m) : Code :=
  sumCodes (List.ofFn (fun i => (get c i).mul (get y i)))

def lengthCode (y : RawRow m) (p : Column m) : Code :=
  sumCodes (List.ofFn (fun i => if i ∈ p then get y i else Code.zero))

@[simp] lemma objectiveCode_value (c y : RawRow m) :
    rational (objectiveCode c y) = objective (decodeRow c) (decodeRow y) := by
  simp [objectiveCode,objective,List.map_ofFn,List.sum_ofFn]

@[simp] lemma lengthCode_value (y : RawRow m) (p : Column m) :
    rational (lengthCode y p) = length (decodeRow y) p := by
  simp [lengthCode,length,List.map_ofFn,List.sum_ofFn,apply_ite]

def deltaCode (m : ℕ) : Code := (Code.ofNat 2).div (Code.ofNat (3*m^2))

def initialCode (c : RawRow m) : RawRow m :=
  let delta := deltaCode m
  Vector.ofFn (fun i => delta.div (get c i))

def normalizedCode (y : RawRow m) (p : Column m) : RawRow m :=
  let alpha := lengthCode y p
  Vector.ofFn (fun i => (get y i).div alpha)

def factorCode (c : RawRow m) (i j : Fin m) : Code :=
  Code.one.add ((get c j).div ((Code.ofNat 2).mul (get c i)))

def updateCode (c y : RawRow m) (q : Choice m) : RawRow m :=
  Vector.ofFn (fun i => if i ∈ q.column then (get y i).mul (factorCode c i q.bottleneck)
    else get y i)

@[simp] lemma deltaCode_value (m : ℕ) : rational (deltaCode m) = delta m := by
  simp [deltaCode,delta]

@[simp] lemma initialCode_value (c : RawRow m) : decodeRow (initialCode c) = initial (decodeRow c) := by
  apply Vector.ext
  intro i hi
  simp [decodeRow,initialCode,initial]

@[simp] lemma normalizedCode_value (y : RawRow m) (p : Column m) :
    decodeRow (normalizedCode y p) = normalized (decodeRow y) p := by
  apply Vector.ext
  intro i hi
  simp [decodeRow,normalizedCode,normalized]

@[simp] lemma factorCode_value (c : RawRow m) (i j : Fin m) :
    rational (factorCode c i j) = 1+value (decodeRow c) j/(2*value (decodeRow c) i) := by
  simp [factorCode]

@[simp] lemma updateCode_value (c y : RawRow m) (q : Choice m) :
    decodeRow (updateCode c y q) = update (decodeRow c) (decodeRow y) q := by
  apply Vector.ext
  intro i hi
  by_cases h : (⟨i,hi⟩ : Fin m) ∈ q.column <;>
    simp [decodeRow,updateCode,update,h]

abbrev RawOracle (m : ℕ) := RawRow m → Choice m

def Refines (raw : RawOracle m) (rat : Oracle m) : Prop :=
  ∀ y, raw y = rat (decodeRow y)

structure RawEvent (m : ℕ) where
  choice : Choice m
  amount : Code

structure RawState (m : ℕ) where
  weights : RawRow m
  best : RawRow m
  bestCost : Code
  total : Code
  loads : RawRow m
  events : List (RawEvent m)

def decodeEvent (e : RawEvent m) : Event m := ⟨e.choice,rational e.amount⟩

def decodeState (s : RawState m) : State m where
  weights := decodeRow s.weights
  best := decodeRow s.best
  bestCost := rational s.bestCost
  total := rational s.total
  loads := decodeRow s.loads
  events := s.events.map decodeEvent

def start (c : RawRow m) (oracle : RawOracle m) : RawState m :=
  let y := initialCode c
  let w := normalizedCode y (oracle y).column
  { weights := y, best := w, bestCost := objectiveCode c w,
    total := Code.zero, loads := Vector.replicate m Code.zero, events := [] }

def step (c : RawRow m) (oracle : RawOracle m) (s : RawState m) : RawState m :=
  if Code.one.le (objectiveCode c s.weights) then s else
    let q := oracle s.weights
    let b := get c q.bottleneck
    let w := normalizedCode s.weights q.column
    let candidate := objectiveCode c w
    let improve := !(s.bestCost.le candidate)
    { weights := updateCode c s.weights q
      best := if improve then w else s.best
      bestCost := if improve then candidate else s.bestCost
      total := s.total.add b
      loads := Vector.ofFn (fun i => (get s.loads i).add (if i ∈ q.column then b else Code.zero))
      events := ⟨q,b⟩ :: s.events }

def run (c : RawRow m) (oracle : RawOracle m) : ℕ → RawState m
  | 0 => start c oracle
  | k+1 => step c oracle (run c oracle k)

def solve (c : RawRow m) (oracle : RawOracle m) : RawState m := run c oracle (fuel m)

lemma decode_replicate (q : Code) :
    decodeRow (Vector.replicate m q) = Vector.replicate m (rational q) := by
  apply Vector.ext
  intro i hi
  simp [decodeRow,get]

lemma start_refines (c : RawRow m) (raw : RawOracle m) (rat : Oracle m) (ho : Refines raw rat) :
    decodeState (start c raw) = FractionalCover.start (decodeRow c) rat := by
  unfold Refines at ho
  unfold start FractionalCover.start decodeState
  simp only [ho,normalizedCode_value,initialCode_value,objectiveCode_value,
    rational_zero,decode_replicate,List.map_nil]

lemma step_refines (c : RawRow m) (raw : RawOracle m) (rat : Oracle m) (ho : Refines raw rat)
    (s : RawState m) :
    decodeState (step c raw s) = FractionalCover.step (decodeRow c) rat (decodeState s) := by
  have hstop : Code.one.le (objectiveCode c s.weights) = true ↔
      1 ≤ objective (decodeRow c) (decodeRow s.weights) := by
    rw [code_le_iff,rational_one,objectiveCode_value]
  by_cases hs : 1 ≤ objective (decodeRow c) (decodeRow s.weights)
  · simp [step,FractionalCover.step,hstop.mpr hs,decodeState,hs]
  · have hsn : Code.one.le (objectiveCode c s.weights) = false :=
      Bool.eq_false_iff.mpr (fun h => hs (hstop.mp h))
    have hchoice := ho s.weights
    let q := rat (decodeRow s.weights)
    let w := normalizedCode s.weights q.column
    have hcomp : s.bestCost.le (objectiveCode c w) = true ↔
        rational s.bestCost ≤ objective (decodeRow c) (normalized (decodeRow s.weights) q.column) := by
      rw [code_le_iff,objectiveCode_value]
      simp only [w,normalizedCode_value]
    by_cases hi : objective (decodeRow c) (normalized (decodeRow s.weights) q.column) < rational s.bestCost
    · have hb : s.bestCost.le (objectiveCode c w) = false :=
        Bool.eq_false_iff.mpr (fun h => (not_le_of_gt hi) (hcomp.mp h))
      simp only [step,hsn,Bool.false_eq_true,ite_false,hchoice]
      simp only [FractionalCover.step,decodeState,hs,ite_false]
      have hloads : decodeRow (Vector.ofFn (fun i => (get s.loads i).add
          (if i ∈ q.column then get c q.bottleneck else Code.zero))) =
          Vector.ofFn (fun i => value (decodeRow s.loads) i+
            if i ∈ q.column then value (decodeRow c) q.bottleneck else 0) := by
        apply Vector.ext
        intro i hi'
        by_cases hm : (⟨i,hi'⟩ : Fin m) ∈ q.column <;> simp [decodeRow,get,hm]
      simp [q,w,hb,hi,min_eq_left hi.le,hloads,decodeEvent]
    · have hb := hcomp.mpr (le_of_not_gt hi)
      have hloads : decodeRow (Vector.ofFn (fun i => (get s.loads i).add
          (if i ∈ q.column then get c q.bottleneck else Code.zero))) =
          Vector.ofFn (fun i => value (decodeRow s.loads) i+
            if i ∈ q.column then value (decodeRow c) q.bottleneck else 0) := by
        apply Vector.ext
        intro i hi'
        by_cases hm : (⟨i,hi'⟩ : Fin m) ∈ q.column <;> simp [decodeRow,get,hm]
      simp [step,FractionalCover.step,decodeState,hsn,hs,hchoice,q,w,hb,hi,
        min_eq_right (le_of_not_gt hi),hloads,decodeEvent]

theorem run_refines (c : RawRow m) (raw : RawOracle m) (rat : Oracle m) (ho : Refines raw rat)
    (k : ℕ) : decodeState (run c raw k) = FractionalCover.run (decodeRow c) rat k := by
  induction k with
  | zero => exact start_refines c raw rat ho
  | succ k ih => rw [run,FractionalCover.run,step_refines c raw rat ho,ih]

theorem solve_refines (c : RawRow m) (raw : RawOracle m) (rat : Oracle m) (ho : Refines raw rat) :
    decodeState (solve c raw) = FractionalCover.solve (decodeRow c) rat :=
  run_refines c raw rat ho (fuel m)

/-- Exact transferred feasibility, stopping and real-comparator approximation.
The provider theorem is erased; only the raw oracle is executed. -/
theorem solve_correct (c : RawRow m) (raw : RawOracle m) (rat : Oracle m) (ho : Refines raw rat)
    (columns : Set (Column m)) (hm : 0 < m) (hc : ∀ i, 0 < value (decodeRow c) i)
    (hor : OracleCorrect (decodeRow c) columns rat) :
    Feasible columns (decodeRow (solve c raw).best) ∧
    1 ≤ objective (decodeRow c) (decodeRow (solve c raw).weights) ∧
    ∀ w : Fin m → ℝ, RealFeasible columns w →
      (objective (decodeRow c) (decodeRow (solve c raw).best) : ℝ) ≤
        3*∑ i,(value (decodeRow c) i : ℝ)*w i := by
  have he := solve_refines c raw rat ho
  have hbest := congrArg State.best he
  have hweights := congrArg State.weights he
  dsimp only [decodeState] at hbest hweights
  rw [hbest,hweights]
  exact ⟨FractionalCover.solve_feasible _ columns rat hm hc hor,
    FractionalCover.solve_stopped _ columns rat hm hc hor,
    fun w hw => solve_three_approximation_real _ columns rat hm hc hor w hw⟩

/-- Recorded events are exactly the executed updates, even without an oracle
contract. A stopped raw state creates no additional event or oracle call. -/
lemma run_event_count (c : RawRow m) (oracle : RawOracle m) (k : ℕ) :
    (run c oracle k).events.length ≤ k := by
  induction k with
  | zero => simp [run,start]
  | succ k ih =>
    simp only [run,step]
    split
    · exact ih.trans (Nat.le_succ k)
    · exact Nat.succ_le_succ ih

def oracleCalls (s : RawState m) : ℕ := s.events.length+1

lemma solve_oracle_calls (c : RawRow m) (oracle : RawOracle m) :
    oracleCalls (solve c oracle) ≤ 3*m^2+1 :=
  Nat.add_le_add_right (run_event_count c oracle (fuel m)) 1

end DirectedFlowCutGap.FractionalCoverRawCore
