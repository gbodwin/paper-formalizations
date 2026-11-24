import DirectedFlowCutGap.MeasuredMultiplicityCover

/-! Bound the arithmetic trace of the measured covering recurrence using
the actual raw rational fields at every reached step. -/
namespace DirectedFlowCutGap.MeasuredMultiplicityCoverBounds

open FractionalCoverRawCore (RawRow RowBounded get)
open MultiplicityCoverWidths (weightWidth normalizedWidth objectiveWidth loadWidth ColumnFits)
open MeasuredMultiplicityCover (Stored MeasuredOracle Execution start advance run)
open MeasuredMultiplicityForms (dot dotWork normalize normalizeWork)
open MeasuredMultiplicityUpdate (operandWidth)
open MeasuredMultiplicityLoads (loadWork)
open RawNonnegativeRational (Code)

variable {r : ℕ}

structure Fields (s : Stored r) (B U k : ℕ) : Prop where
  weights : RowBounded s.weights (weightWidth r B U k)
  best : RowBounded s.best (normalizedWidth r U (weightWidth r B U k))
  bestCost : s.bestCost.Bounded (objectiveWidth r B (normalizedWidth r U (weightWidth r B U k)))
  total : s.total.Bounded (loadWidth B U k)
  loads : RowBounded s.loads (loadWidth B U k)

private theorem fields_mono (s : Stored r) {B U k t : ℕ} (fields : Fields s B U k) (later : k ≤ t) :
    Fields s B U t := by
  have w : weightWidth r B U k ≤ weightWidth r B U t := by unfold weightWidth; gcongr
  have best : normalizedWidth r U (weightWidth r B U k) ≤ normalizedWidth r U (weightWidth r B U t) := by
    unfold normalizedWidth
    gcongr
  have cost : objectiveWidth r B (normalizedWidth r U (weightWidth r B U k)) ≤
      objectiveWidth r B (normalizedWidth r U (weightWidth r B U t)) := by
    unfold objectiveWidth
    gcongr
  have load : loadWidth B U k ≤ loadWidth B U t := by unfold loadWidth; gcongr
  exact ⟨fun i => Code.bounded_mono (fields.weights i) w,fun i => Code.bounded_mono (fields.best i) best,
    Code.bounded_mono fields.bestCost cost,Code.bounded_mono fields.total load,
    fun i => Code.bounded_mono (fields.loads i) load⟩

def startWork (r B U : ℕ) : ℕ :=
  let W := weightWidth r B U 0
  (r+3)*BinaryRawRational.budget W + normalizeWork r U W + dotWork r B (normalizedWidth r U W)

def advanceWork (r B U k : ℕ) : ℕ :=
  let W := weightWidth r B U k
  let N := normalizedWidth r U W
  let C := objectiveWidth r B N
  let L := loadWidth B U k
  dotWork r B W + BinaryRawRational.budget (objectiveWidth r B W) +
    normalizeWork r U W + dotWork r B N + BinaryRawRational.budget C +
    (1+r*5)*BinaryRawRational.budget (operandWidth B U W) + loadWork r B U L

theorem advanceWork_mono (r B U : ℕ) {k t : ℕ} (later : k ≤ t) :
    advanceWork r B U k ≤ advanceWork r B U t := by
  simp only [advanceWork,normalizeWork,dotWork,normalizedWidth,objectiveWidth,loadWidth,
    loadWork,operandWidth,BinaryRawRational.budget,weightWidth]
  gcongr

theorem start_bounds (c : RawRow r) (oracle : MeasuredOracle r) {B U : ℕ} (price : RowBounded c B)
    (counts : ∀ y, ColumnFits (oracle y).1.column U) :
    Fields (start c oracle).stored B U 0 ∧ (start c oracle).arithmetic ≤ startWork r B U := by
  let y := MeasuredMultiplicityLoads.start c
  let p := (oracle y.1).1.column
  let z := normalize y.1 p
  have hi := MeasuredMultiplicityLoads.start_bounds c price
  have a : RowBounded y.1 (weightWidth r B U 0) := by
    simpa only [weightWidth,Nat.zero_mul,Nat.add_zero] using hi.1
  obtain ⟨zFit,zWork⟩ := MeasuredMultiplicityForms.normalize_bounds y.1 p a (counts y.1)
  have zFields : RowBounded z.1 (normalizedWidth r U (weightWidth r B U 0)) := by
    simpa only [z,normalizedWidth,Nat.add_comm U (weightWidth r B U 0)] using zFit
  have j := MeasuredMultiplicityForms.dot_bounds c z.1 price zFields
  constructor
  · refine ⟨a,zFields,j.1,?_,?_⟩
    · simpa only [start,loadWidth,Nat.zero_mul] using Code.bounded_zero
    · intro i
      simpa only [start,loadWidth,Nat.zero_mul,FractionalCoverRawCore.get,Vector.getElem_replicate] using Code.bounded_zero
  · have cost : y.2 ≤ (r+3)*BinaryRawRational.budget (weightWidth r B U 0) := by
      simpa only [weightWidth,Nat.zero_mul,Nat.add_zero] using hi.2
    exact Nat.add_le_add (Nat.add_le_add cost zWork) j.2

theorem advance_bounds (c : RawRow r) (oracle : MeasuredOracle r) (s : Stored r) {B U k : ℕ}
    (price : RowBounded c B) (counts : ∀ y, ColumnFits (oracle y).1.column U) (fields : Fields s B U k) :
    Fields (advance c oracle s).stored B U (k+1) ∧ (advance c oracle s).arithmetic ≤ advanceWork r B U k := by
  let W := weightWidth r B U k
  let N := normalizedWidth r U W
  let C := objectiveWidth r B N
  let L := loadWidth B U k
  let p := (oracle s.weights).1
  let current := dot c s.weights
  let z := normalize s.weights p.column
  let fee := dot c z.1
  let guard := BinaryRawRational.le Code.one current.1
  let keep := BinaryRawRational.le s.bestCost fee.1
  have valid := counts s.weights
  have currentFit := MeasuredMultiplicityForms.dot_bounds c s.weights price fields.weights
  have guardWork : guard.2 ≤ BinaryRawRational.budget (objectiveWidth r B W) :=
    BinaryRawRational.le_paid (Code.bounded_mono Code.bounded_one zero_le) currentFit.1
  have prior := fields_mono s fields (Nat.le_succ k)
  cases checked : guard.1 with
  | true =>
    have stop : (BinaryRawRational.le Code.one (dot c s.weights).1).1 = true := checked
    constructor
    · dsimp only [advance]
      rw [ite_eq_left stop]
      exact prior
    · dsimp only [advance,advanceWork]
      rw [ite_eq_left stop]
      change current.2+guard.2 ≤ _
      have h := Nat.add_le_add currentFit.2 guardWork
      exact h.trans (by dsimp only [W]; omega)
  | false =>
    have reached : ¬ (BinaryRawRational.le Code.one (dot c s.weights).1).1 = true := by
      change ¬ guard.1 = true
      simp only [checked,Bool.false_eq_true,not_false_eq_true]
    obtain ⟨zFit,zWork⟩ := MeasuredMultiplicityForms.normalize_bounds s.weights p.column fields.weights valid
    have nBound : RowBounded z.1 N := by
      change RowBounded z.1 (W+r*(U+W+1)) at zFit
      unfold N normalizedWidth
      rw [Nat.add_comm W U]
      exact zFit
    obtain ⟨feeFit,feeWork⟩ := MeasuredMultiplicityForms.dot_bounds c z.1 price nBound
    have keepWork : keep.2 ≤ BinaryRawRational.budget C :=
      BinaryRawRational.le_paid fields.bestCost feeFit
    obtain ⟨newRow,copyWork⟩ := MeasuredMultiplicityUpdate.run_bounds c s.weights p price fields.weights valid
    obtain ⟨newTotal,newLoads,flowWork⟩ :=
      MeasuredMultiplicityLoads.add_bounds c p s.total s.loads price valid fields.total fields.loads
    have wGrowth : W+(2*B+2*U+2) = weightWidth r B U (k+1) := by unfold W weightWidth; ring
    have lGrowth : L+(B+2*U)+1 = loadWidth B U (k+1) := by unfold L loadWidth; ring
    rw [wGrowth] at newRow
    rw [lGrowth] at newTotal newLoads
    have nextBest : RowBounded z.1 (normalizedWidth r U (weightWidth r B U (k+1))) :=
      fun i => Code.bounded_mono (nBound i) (by unfold N normalizedWidth W weightWidth; gcongr <;> omega)
    have nextFee : fee.1.Bounded (objectiveWidth r B (normalizedWidth r U (weightWidth r B U (k+1)))) :=
      Code.bounded_mono feeFit (by unfold objectiveWidth N normalizedWidth W weightWidth; gcongr <;> omega)
    dsimp only [advance]
    rw [ite_eq_right reached]
    refine ⟨?_,?_⟩
    · cases comparison : keep.1 with
      | false =>
        rw [ite_eq_right (show (false : Bool) ≠ true from Bool.noConfusion)]
        exact ⟨newRow,nextBest,nextFee,newTotal,newLoads⟩
      | true =>
        rw [ite_eq_left (show (true : Bool) = true from rfl)]
        exact ⟨newRow,prior.best,prior.bestCost,newTotal,newLoads⟩
    · unfold advanceWork
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add currentFit.2 guardWork) zWork) feeWork) keepWork) copyWork) flowWork

theorem run_fields (c : RawRow r) (oracle : MeasuredOracle r) {B U : ℕ} (price : RowBounded c B)
    (counts : ∀ y, ColumnFits (oracle y).1.column U) (k : ℕ) : Fields (run c oracle k).stored B U k := by
  induction k with
  | zero => exact (start_bounds c oracle price counts).1
  | succ k ih => exact (advance_bounds c oracle (run c oracle k).stored price counts ih).1

theorem run_charge (c : RawRow r) (oracle : MeasuredOracle r) {B U : ℕ} (price : RowBounded c B)
    (counts : ∀ y, ColumnFits (oracle y).1.column U) (t : ℕ) :
    (run c oracle t).arithmetic ≤ startWork r B U+t*advanceWork r B U t := by
  have below (k : ℕ) (within : k ≤ t) :
      (run c oracle k).arithmetic ≤ startWork r B U+k*advanceWork r B U t := by
    induction k with
    | zero => simpa only [run,Nat.zero_mul,Nat.add_zero] using (start_bounds c oracle price counts).2
    | succ k ih =>
      have prior := ih (Nat.le_of_succ_le within)
      have step := (advance_bounds c oracle (run c oracle k).stored price counts
        (run_fields c oracle price counts k)).2
      have limit := advanceWork_mono r B U (Nat.le_of_succ_le within)
      have h := Nat.add_le_add prior (step.trans limit)
      simpa only [run,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using h
  exact below t le_rfl

theorem run_oracle_charge (c : RawRow r) (oracle : MeasuredOracle r) {B U t C : ℕ}
    (price : RowBounded c B) (counts : ∀ y, ColumnFits (oracle y).1.column U)
    (perCall : ∀ y, RowBounded y (weightWidth r B U t) → (oracle y).2 ≤ C)
    {k : ℕ} (within : k ≤ t) : (run c oracle k).oracleWork ≤ (k+1)*C := by
  induction k with
  | zero =>
    have fit := fields_mono (start c oracle).stored (start_bounds c oracle price counts).1 (Nat.zero_le t)
    simpa only [run,start,Nat.zero_add,Nat.one_mul] using
      perCall (MeasuredMultiplicityLoads.start c).1 fit.weights
  | succ k ih =>
    have time := Nat.le_of_succ_le within
    let prev := run c oracle k
    have fit := fields_mono prev.stored (run_fields c oracle price counts k) time
    have step : (advance c oracle prev.stored).oracleWork ≤ C := by
      dsimp only [advance]
      by_cases stop : (BinaryRawRational.le Code.one (dot c prev.stored.weights).1).1 = true
      · rw [ite_eq_left stop]
        exact Nat.zero_le _
      · rw [ite_eq_right stop]
        exact perCall prev.stored.weights fit.weights
    change prev.oracleWork+(advance c oracle prev.stored).oracleWork ≤ (k+1+1)*C
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add (ih time) step

end DirectedFlowCutGap.MeasuredMultiplicityCoverBounds
