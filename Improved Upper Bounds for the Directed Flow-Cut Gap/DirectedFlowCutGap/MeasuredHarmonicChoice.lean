import DirectedFlowCutGap.MeasuredBudgetPrices
import DirectedFlowCutGap.MeasuredMultiplicityForms
import DirectedFlowCutGap.RationalHarmonicThreshold

/-! Evaluate each harmonic score with binary arithmetic and retain the
first distance of maximum score, as in the reference threshold rule. -/
namespace DirectedFlowCutGap.MeasuredHarmonicChoice

open scoped BigOperators NNRat
open RawNonnegativeRational (Code)
open FractionalCoverRawCore (rational)
open MeasuredBudgetPrices (tabulate tabulate_value tabulate_charge)
open MeasuredMultiplicityForms (sum sum_value sum_charge)

variable {m : ℕ}

private theorem tabulate_get {α : Type*} (f : Fin m → α × ℕ) (i : Fin m) :
    (tabulate f).1.get i = (f i).1 :=
  tabulate_value f i.val i.isLt

private def cell (q d : Code) : Code × ℕ :=
  let compare := BinaryRawRational.le q d
  (if compare.1 then Code.one else Code.zero,compare.2+1)

private def countInputs (d : Fin m → Code) (q : Code) : List Code × ℕ :=
  let checks := tabulate fun j => cell q (d j)
  (List.ofFn fun j => checks.1.get j,checks.2)

def count (d : Fin m → Code) (q : Code) : Code × ℕ :=
  let checked := countInputs d q
  let total := sum checked.1
  (total.1,checked.2+total.2)

theorem count_value (d : Fin m → Code) (q : Code) :
    rational (count d q).1 = RationalHarmonicThreshold.count (fun j => (d j).value) q.value := by
  simp only [count,countInputs,sum_value,FractionalCoverRawCore.rational_sum,List.map_ofFn,
    Function.comp_def,List.sum_ofFn,tabulate_get,cell,BinaryRawRational.le_value,Code.le_eq_true,
    apply_ite,FractionalCoverRawCore.rational_one,FractionalCoverRawCore.rational_zero]
  exact Finset.sum_boole (R := ℚ) (fun j => q.value ≤ (d j).value) Finset.univ

private theorem cell_fits (q d : Code) : (cell q d).1.Bounded 1 := by
  simp only [cell]
  split
  · exact Code.bounded_mono Code.bounded_one (by decide)
  · exact Code.bounded_mono Code.bounded_zero (by decide)

private theorem countInputs_fit (d : Fin m → Code) (q : Code) :
    ∀ a ∈ (countInputs d q).1, a.Bounded 1 := by
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  rw [tabulate_get]
  exact cell_fits q (d i)

private theorem count_fields (d : Fin m → Code) (q : Code) :
    (count d q).1.Bounded (2*m) := by
  have wide := FractionalCoverRawCore.sumCodes_bounded (countInputs d q).1 1 (countInputs_fit d q)
  rw [count,sum_value]
  simpa only [countInputs,List.length_ofFn,Nat.reduceAdd,Nat.mul_comm m 2] using wide

def countWork (m W : ℕ) : ℕ :=
  m*(BinaryRawRational.budget W+1)+m*BinaryRawRational.budget (2*m)

theorem count_charge (d : Fin m → Code) (q : Code) {W : ℕ}
    (fits : ∀ i, (d i).Bounded W) (threshold : q.Bounded W) :
    (count d q).2 ≤ countWork m W := by
  let input := (countInputs d q).1
  have sumWork := sum_charge input (countInputs_fit d q) (show input.length ≤ m from by simp [input,countInputs])
  have tests := tabulate_charge (fun j => cell q (d j))
    (fun j => Nat.add_le_add_right (BinaryRawRational.le_paid threshold (fits j)) 1)
  exact Nat.add_le_add tests (by
    simpa only [input,countInputs,List.length_ofFn,Nat.reduceAdd,Nat.mul_comm m 2] using sumWork)

def score (d : Fin m → Code) (i : Fin m) : Code × ℕ :=
  let visits := count d (d i)
  let product := BinaryRawRational.mul (d i) visits.1
  (product.1,visits.2+product.2)

theorem score_value (d : Fin m → Code) (i : Fin m) :
    rational (score d i).1 = (RationalHarmonicThreshold.score (fun j => (d j).value) i : ℚ) := by
  change rational (BinaryRawRational.mul (d i) (count d (d i)).1).1 = _
  rw [BinaryRawRational.mul_value,FractionalCoverRawCore.rational_mul,count_value]
  simp only [RationalHarmonicThreshold.score,NNRat.cast_mul,NNRat.cast_natCast,rational]

def scoreWork (m W : ℕ) : ℕ := countWork m W+BinaryRawRational.budget (W+2*m)

theorem score_bounds (d : Fin m → Code) (i : Fin m) {W : ℕ} (fits : ∀ j, (d j).Bounded W) :
    (score d i).1.Bounded (W+2*m) ∧ (score d i).2 ≤ scoreWork m W := by
  have f := count_fields d (d i)
  constructor
  · simp only [score,BinaryRawRational.mul_value]
    exact Code.bounded_mul (fits i) f
  · exact Nat.add_le_add (count_charge d (d i) fits (fits i))
      (BinaryRawRational.mul_paid (Code.bounded_mono (fits i) (Nat.le_add_right ..))
        (Code.bounded_mono f (Nat.le_add_left ..)))

private def pick (scored : Fin m → Code) (i : Fin m) : Option (Fin m) → Option (Fin m) × ℕ
  | none => (some i,1)
  | some j =>
    let compare := BinaryRawRational.le (scored i) (scored j)
    (some (if compare.1 then j else i),compare.2+4)

private theorem pick_value (scored : Fin m → Code) (i : Fin m) (winner : Option (Fin m)) :
    (pick scored i winner).1 = List.argAux (fun a b => (scored b).value < (scored a).value) winner i := by
  cases winner with
  | none => rfl
  | some j =>
    simp only [pick,List.argAux,BinaryRawRational.le_value,Code.le_eq_true]
    by_cases smaller : (scored j).value < (scored i).value
    · rw [ite_eq_right (not_le_of_gt smaller),ite_eq_left smaller]
    · rw [ite_eq_left (le_of_not_gt smaller),ite_eq_right smaller]

private def pickAll (scored : Fin m → Code) : List (Fin m) → Option (Fin m) → Option (Fin m) × ℕ
  | [],winner => (winner,1)
  | i::rest,winner =>
    let chosen := pick scored i winner
    let next := pickAll scored rest chosen.1
    (next.1,chosen.2+next.2+4)

private theorem pickAll_value (scored : Fin m → Code) (xs : List (Fin m)) (winner : Option (Fin m)) :
    (pickAll scored xs winner).1 =
      xs.foldl (List.argAux fun a b => (scored b).value < (scored a).value) winner := by
  induction xs generalizing winner with
  | nil => rfl
  | cons i rest ih => simp only [pickAll,ih,pick_value,List.foldl_cons]

private theorem pickAll_charge (scored : Fin m → Code) (xs : List (Fin m)) (winner : Option (Fin m))
    {W : ℕ} (fits : ∀ j, (scored j).Bounded W) :
    (pickAll scored xs winner).2 ≤ xs.length*(BinaryRawRational.budget W+8)+1 := by
  induction xs generalizing winner with
  | nil => simp [pickAll]
  | cons i rest ih =>
    have localWork : (pick scored i winner).2 ≤ BinaryRawRational.budget W+4 := by
      cases winner with
      | none => simp only [pick]; omega
      | some j => exact Nat.add_le_add_right (BinaryRawRational.le_paid (fits i) (fits j)) 4
    have tail := ih (pick scored i winner).1
    simp only [pickAll,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def choose (d : Fin m → Code) : Option (Fin m) × ℕ :=
  let computed := tabulate (score d)
  let selected := pickAll (fun i => computed.1.get i) (List.finRange m) none
  (selected.1,computed.2+selected.2)

theorem choose_value (d : Fin m → Code) :
    (choose d).1 = RationalHarmonicThreshold.choose (fun j => (d j).value) := by
  have values (j : Fin m) : (score d j).1.value = RationalHarmonicThreshold.score (fun x => (d x).value) j :=
    NNRat.coe_injective (score_value d j)
  have ranks : (fun j => ((tabulate (score d)).1.get j).value) =
      RationalHarmonicThreshold.score (fun j => (d j).value) := by
    funext j
    rw [tabulate_get,values]
  simp only [choose,pickAll_value]
  change (List.finRange m).argmax (fun j => ((tabulate (score d)).1.get j).value) = _
  rw [ranks]
  rfl

def chooseWork (m W : ℕ) : ℕ :=
  m*scoreWork m W+m*(BinaryRawRational.budget (W+2*m)+8)+1

theorem choose_charge (d : Fin m → Code) {W : ℕ} (fits : ∀ j, (d j).Bounded W) :
    (choose d).2 ≤ chooseWork m W := by
  have scores := tabulate_charge (score d) (fun j => (score_bounds d j fits).2)
  have picked := pickAll_charge (fun i => (tabulate (score d)).1.get i) (List.finRange m) none
    (fun j => by rw [tabulate_get]; exact (score_bounds d j fits).1)
  simpa only [choose,chooseWork,List.length_finRange,Nat.add_assoc] using Nat.add_le_add scores picked

end DirectedFlowCutGap.MeasuredHarmonicChoice
