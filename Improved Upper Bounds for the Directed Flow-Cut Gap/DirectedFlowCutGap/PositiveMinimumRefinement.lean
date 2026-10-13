import DirectedFlowCutGap.PositiveMinimumValue

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic BinaryRational

def datum {α : Type*} (score : α → Fraction × ℕ) (label : α → Bits) (x : α) : Bits × Fraction :=
  (label x,(score x).1)

theorem from_refines {α : Type*} (score : α → BinaryRational.Fraction × ℕ)
    (label : α → Bits) (xs : List α) (a : α) :
    some (minFrom (datum score label a) (xs.map (datum score label)))=
      (BinaryFractionalGraphOracle.argminFrom score xs (some a)).1.map (datum score label) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,minFrom,choose,datum,
      BinaryFractionalGraphOracle.argminFrom,BinaryFractionalGraphOracle.argminAux]
    by_cases hc : (BinaryRational.le (score a).1 (score x).1).1=true
    · simpa only [datum,hc,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
        using ih a
    · have hf : (BinaryRational.le (score a).1 (score x).1).1=false :=
        Bool.eq_false_iff.mpr hc
      simpa only [datum,hf,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
        using ih x

theorem value_refines {α : Type*} (score : α → BinaryRational.Fraction × ℕ)
    (label : α → Bits) (xs : List α) :
    select (xs.map (datum score label))=
      (BinaryFractionalGraphOracle.argmin score xs).1.map (datum score label) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    exact from_refines score label xs x


theorem original_value {n : ℕ} (c : BinaryFractionalRows.Row n) (label : Fin n → Bits) :
    select (PositiveInventory.selected (((List.finRange n).map label).zip c.toList))=
      (BinaryFractionalDispatch.minimumPositive c).1.map
        (fun i => (label i,BinaryFractionalRows.get c i)) := by
  rw [PositiveInventory.selected_original]
  exact value_refines (BinaryFractionalGraphOracle.read c) label _
end DirectedFlowCutGap.PositiveMinimum
