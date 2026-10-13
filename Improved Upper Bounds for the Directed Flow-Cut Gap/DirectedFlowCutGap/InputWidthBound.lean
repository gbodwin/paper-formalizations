import DirectedFlowCutGap.InputWidthTrace
import DirectedFlowCutGap.SourceRowTableProgram

namespace DirectedFlowCutGap.InputWidthProgram
open BinaryArithmetic BinaryRational

def bits (rows : List Fraction) : ℕ := SourceRowTableProgram.bits (IndexedRationalRead.fields rows)

theorem fraction_length (q : Fraction) :
    (BinaryFractionalGuesses.fractionWidth q).1.length ≤ q.num.length+q.den.length := by
  have hn := FractionWidthProgram.size_length q.num
  have hd := FractionWidthProgram.size_length q.den
  simp only [BinaryFractionalGuesses.fractionWidth,BinaryFractionalGuesses.maximum]
  split <;> omega

theorem width_length (rows : List Fraction) : (BinaryFractionalGuesses.widthList rows).1.length ≤ bits rows := by
  induction rows with
  | nil => simp [BinaryFractionalGuesses.widthList,bits,IndexedRationalRead.fields,SourceRowTableProgram.bits]
  | cons q qs ih =>
    have h := fraction_length q
    simp only [BinaryFractionalGuesses.widthList,BinaryFractionalGuesses.maximum,bits,
      IndexedRationalRead.fields,List.map_cons,SourceRowTableProgram.bits]
    dsimp only [bits,IndexedRationalRead.fields] at ih
    split <;> omega

theorem steps_bound (rows : List Fraction) : steps rows ≤ (160*(bits rows+1)^2+32)*rows.length+3 := by
  induction rows with
  | nil => simp [steps]
  | cons q qs ih =>
    have hf := FractionWidthProgram.steps_bound q
    have hm := BinaryMaximumProgram.steps_bound
      (BinaryFractionalGuesses.fractionWidth q).1 (BinaryFractionalGuesses.widthList qs).1
    have hl := fraction_length q
    have hr := width_length qs
    have hb : bits (q::qs)=q.num.length+q.den.length+bits qs := rfl
    have ht : (160*(bits qs+1)^2+32)*qs.length ≤
        (160*(bits (q::qs)+1)^2+32)*qs.length := by rw [hb];gcongr;omega
    have hsq : (q.num.length+q.den.length+1)^2 ≤ (bits (q::qs)+1)^2 := by
      have hg : q.num.length+q.den.length+1 ≤ bits (q::qs)+1 := by omega
      exact Nat.pow_le_pow_left hg 2
    have hm' : BinaryMaximumProgram.steps (BinaryFractionalGuesses.fractionWidth q).1
        (BinaryFractionalGuesses.widthList qs).1 ≤ 24*(bits (q::qs)+1) := by
      unfold BinaryMaximumProgram.inputSteps at hm
      omega
    unfold FractionWidthProgram.inputSteps at hf
    simp only [steps,List.length_cons,Nat.mul_add,Nat.mul_one]
    nlinarith

def inputSteps (rows : List Fraction) : ℕ := (160*(bits rows+1)^2+32)*rows.length+4
end DirectedFlowCutGap.InputWidthProgram
