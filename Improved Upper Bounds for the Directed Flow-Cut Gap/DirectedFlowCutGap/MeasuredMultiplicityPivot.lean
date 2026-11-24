import DirectedFlowCutGap.MeasuredMultiplicityUpdate
import DirectedFlowCutGap.BinaryFractionalGraphBounds

/-! The covering oracle's bottleneck comparison uses the exact fraction
price divided by path multiplicity. This measures those divisions,
encodings, and comparisons and preserves the first minimizer. -/
namespace DirectedFlowCutGap.MeasuredMultiplicityPivot

open RawNonnegativeRational (Code)
open FractionalCoverRawCore (RawRow RowBounded get decodeRow rational)
open MultiplicityCover (Column coeff)
open MultiplicityCoverWidths (ColumnFits)
open BinaryFractionalGraphBounds (argminBound)

variable {r : ℕ}

def active (p : Column r) : List (Fin r) :=
  (List.finRange r).filter fun i => decide (0 < coeff p i)

def rate (c : RawRow r) (p : Column r) (i : Fin r) : BinaryRational.Fraction × ℕ :=
  let divided := BinaryRawRational.div (get c i) (Code.ofNat (coeff p i))
  let encoded := BinaryRawRational.encode divided.1
  (encoded.1,divided.2+encoded.2)

def choose (rpos : 0 < r) (c : RawRow r) (p : Column r) : Fin r × ℕ :=
  let arg := BinaryFractionalGraphOracle.argmin (rate c p) (active p)
  (arg.1.getD ⟨0,rpos⟩,arg.2)

theorem choose_value (rpos : 0 < r) (c : RawRow r) (p : Column r) :
    (choose rpos c p).1 = ((active p).argmin
      (fun i => FractionalCover.value (decodeRow c) i / (coeff p i : ℚ))).getD ⟨0,rpos⟩ := by
  simp only [choose,BinaryFractionalGraphOracle.argmin_decode,FractionalCoverRawGraph.argminCode_refines,
    rate,BinaryRawRational.encode_value,BinaryRawRational.div_value,FractionalCoverRawCore.rational_div,
    FractionalCoverRawCore.rational_nat,FractionalCoverRawCore.decode_value]

def work (r B U : ℕ) : ℕ :=
  argminBound r (B+U+1) (BinaryRawRational.budget (max B U)+40*(B+U+2)^2)

attribute [local irreducible] BinaryRawRational.div BinaryRawRational.encode in
theorem choose_charge (rpos : 0 < r) (c : RawRow r) (p : Column r) {B U : ℕ}
    (price : RowBounded c B) (column : ColumnFits p U) : (choose rpos c p).2 ≤ work r B U := by
  have each (i : Fin r) : BinaryRational.StoredBounded (rate c p i).1 (B+U+1) ∧
      (rate c p i).2 ≤ BinaryRawRational.budget (max B U)+40*(B+U+2)^2 := by
    let count := Code.ofNat (coeff p i)
    let divided := BinaryRawRational.div (get c i) count
    have countFit := MeasuredMultiplicityUpdate.ofNat_fits (column i)
    have fit : divided.1.Bounded (B+U) := by
      change (BinaryRawRational.div (get c i) count).1.Bounded (B+U)
      rw [BinaryRawRational.div_value]
      exact Code.bounded_div (price i) countFit
    have division := BinaryRawRational.div_paid
      (Code.bounded_mono (price i) (le_max_left B U)) (Code.bounded_mono countFit (le_max_right B U))
    change BinaryRational.StoredBounded (BinaryRawRational.encode divided.1).1 (B+U+1) ∧
      divided.2+(BinaryRawRational.encode divided.1).2 ≤ _
    exact ⟨BinaryRawRational.encode_width fit,
      Nat.add_le_add division (BinaryRawRational.encode_paid fit)⟩
  have candidates : (active p).length ≤ r := by
    simpa only [active,List.length_finRange] using
      List.length_filter_le (fun i => decide (0 < coeff p i)) (List.finRange r)
  exact (BinaryFractionalGraphBounds.argmin_charge (rate c p) (active p) (fun i _ => each i)).trans
    (BinaryFractionalGraphBounds.argminBound_mono candidates)

end DirectedFlowCutGap.MeasuredMultiplicityPivot
