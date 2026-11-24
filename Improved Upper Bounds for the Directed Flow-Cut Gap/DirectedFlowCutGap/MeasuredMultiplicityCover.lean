import DirectedFlowCutGap.MeasuredMultiplicityLoads

/-! The measured rational cover follows the actual stopping test, candidate
choice, normalization, objective comparison and multiplicity update.
The oracle reports its own work separately from the state's arithmetic. -/
namespace DirectedFlowCutGap.MeasuredMultiplicityCover

open RawNonnegativeRational (Code)
open FractionalCover (objective initial value)
open FractionalCoverRawCore (RawRow rational decodeRow)
open MultiplicityCover (Choice State Oracle)
open MeasuredMultiplicityForms (dot normalize)

variable {r : ℕ}

structure Stored (r : ℕ) where
  weights : RawRow r
  best : RawRow r
  bestCost : Code
  total : Code
  loads : RawRow r

def decoded (s : Stored r) : State r :=
  ⟨decodeRow s.weights,decodeRow s.best,rational s.bestCost,rational s.total,decodeRow s.loads⟩

abbrev MeasuredOracle (r : ℕ) := RawRow r → Choice r × ℕ

def Refines (measured : MeasuredOracle r) (plain : Oracle r) : Prop :=
  ∀ y, (measured y).1 = plain (decodeRow y)

structure Execution (r : ℕ) where
  stored : Stored r
  arithmetic : ℕ
  oracleWork : ℕ

def start (c : RawRow r) (oracle : MeasuredOracle r) : Execution r :=
  let y := MeasuredMultiplicityLoads.start c
  let pick := oracle y.1
  let best := normalize y.1 pick.1.column
  let fee := dot c best.1
  ⟨⟨y.1,best.1,fee.1,Code.zero,Vector.replicate r Code.zero⟩,
    y.2+best.2+fee.2,pick.2⟩

def advance (c : RawRow r) (oracle : MeasuredOracle r) (s : Stored r) : Execution r :=
  let current := dot c s.weights
  let stop := BinaryRawRational.le Code.one current.1
  if stop.1 then ⟨s,current.2+stop.2,0⟩ else
    let pick := oracle s.weights
    let possible := normalize s.weights pick.1.column
    let fee := dot c possible.1
    let keep := BinaryRawRational.le s.bestCost fee.1
    let weights := MeasuredMultiplicityUpdate.run c s.weights pick.1
    let load := MeasuredMultiplicityLoads.add c pick.1 s.total s.loads
    let best := if keep.1 then (s.best,s.bestCost) else (possible.1,fee.1)
    ⟨⟨weights.1,best.1,best.2,load.total,load.loads⟩,
      current.2+stop.2+possible.2+fee.2+keep.2+weights.2+load.charge,pick.2⟩

def run (c : RawRow r) (oracle : MeasuredOracle r) : ℕ → Execution r
  | 0 => start c oracle
  | k+1 =>
    let prev := run c oracle k
    let next := advance c oracle prev.stored
    ⟨next.stored,prev.arithmetic+next.arithmetic,prev.oracleWork+next.oracleWork⟩

private theorem compare (a b : Code) :
    (BinaryRawRational.le a b).1 = true ↔ rational a ≤ rational b := by
  rw [BinaryRawRational.le_value,FractionalCoverRawCore.code_le_iff]

private theorem zero_weights (r : ℕ) :
    decodeRow (Vector.replicate r Code.zero) = Vector.replicate r 0 := by
  apply Vector.ext
  intro i hi
  simp only [decodeRow,FractionalCoverRawCore.get,Vector.getElem_ofFn,Vector.getElem_replicate,
    FractionalCoverRawCore.rational_zero]

theorem start_value (c : RawRow r) (measured : MeasuredOracle r) (plain : Oracle r)
    (exactChoice : Refines measured plain) :
    decoded (start c measured).stored = MultiplicityCover.start (decodeRow c) plain := by
  have chosen := exactChoice (MeasuredMultiplicityLoads.start c).1
  simp only [start,decoded,MultiplicityCover.start,MeasuredMultiplicityForms.dot_value,
    MeasuredMultiplicityForms.normalize_value,chosen,MeasuredMultiplicityLoads.start_value,
    FractionalCoverRawCore.rational_zero,zero_weights]

theorem advance_value (c : RawRow r) (measured : MeasuredOracle r) (plain : Oracle r)
    (exactChoice : Refines measured plain) (s : Stored r) :
    decoded (advance c measured s).stored = MultiplicityCover.step (decodeRow c) plain (decoded s) := by
  have guard : (BinaryRawRational.le Code.one (dot c s.weights).1).1 = true ↔
      1 ≤ objective (decodeRow c) (decodeRow s.weights) := by
    rw [compare,FractionalCoverRawCore.rational_one,MeasuredMultiplicityForms.dot_value]
  by_cases stop : 1 ≤ objective (decodeRow c) (decodeRow s.weights)
  · have unchanged : (advance c measured s).stored = s := by
      dsimp only [advance]
      rw [ite_eq_left (guard.mpr stop)]
    rw [unchanged]
    dsimp only [MultiplicityCover.step,decoded]
    rw [ite_eq_left stop]
  · have reached : ¬ (BinaryRawRational.le Code.one (dot c s.weights).1).1 = true :=
      fun flag => stop (guard.mp flag)
    let selected := (measured s.weights).1
    let filtered := normalize s.weights selected.column
    let fee := dot c filtered.1
    let price := objective (decodeRow c)
      (MultiplicityCover.normalized (decodeRow s.weights) (plain (decodeRow s.weights)).column)
    have sameChoice : selected = plain (decodeRow s.weights) := exactChoice s.weights
    have feeRead : rational fee.1 = price := by
      simp only [fee,MeasuredMultiplicityForms.dot_value,filtered,MeasuredMultiplicityForms.normalize_value,
        sameChoice,price]
    have keeping : (BinaryRawRational.le s.bestCost fee.1).1 = true ↔ rational s.bestCost ≤ price := by
      rw [compare,feeRead]
    have active : (advance c measured s).stored =
          (⟨(MeasuredMultiplicityUpdate.run c s.weights selected).1,
            (if (BinaryRawRational.le s.bestCost fee.1).1 then (s.best,s.bestCost)
              else (filtered.1,fee.1)).1,
            (if (BinaryRawRational.le s.bestCost fee.1).1 then (s.best,s.bestCost)
              else (filtered.1,fee.1)).2,
            (MeasuredMultiplicityLoads.add c selected s.total s.loads).total,
            (MeasuredMultiplicityLoads.add c selected s.total s.loads).loads⟩ : Stored r) := by
      dsimp only [advance]
      rw [ite_eq_right reached]
    rw [active]
    dsimp only [decoded,MultiplicityCover.step]
    rw [ite_eq_right stop]
    by_cases better : price < rational s.bestCost
    · have newer : ¬ (BinaryRawRational.le s.bestCost fee.1).1 = true :=
        fun flag => (not_le_of_gt better) (keeping.mp flag)
      rw [ite_eq_right newer,ite_eq_left better,min_eq_left better.le]
      simp only [MeasuredMultiplicityUpdate.run_value,MeasuredMultiplicityLoads.add_total,
        MeasuredMultiplicityLoads.add_loads,filtered,MeasuredMultiplicityForms.normalize_value,sameChoice,feeRead]
    · have prior := le_of_not_gt better
      rw [ite_eq_left (keeping.mpr prior),ite_eq_right better,min_eq_right prior]
      simp only [MeasuredMultiplicityUpdate.run_value,MeasuredMultiplicityLoads.add_total,
        MeasuredMultiplicityLoads.add_loads,sameChoice]

theorem run_value (c : RawRow r) (measured : MeasuredOracle r) (plain : Oracle r)
    (exactChoice : Refines measured plain) (k : ℕ) :
    decoded (run c measured k).stored = MultiplicityCover.run (decodeRow c) plain k := by
  induction k with
  | zero => exact start_value c measured plain exactChoice
  | succ k ih => simp only [run,advance_value c measured plain exactChoice,MultiplicityCover.run,ih]

end DirectedFlowCutGap.MeasuredMultiplicityCover
