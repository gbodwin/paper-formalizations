import DirectedFlowCutGap.PackingParametersConstants

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic BinaryRational BinaryFractionalRows

def dimensionWord (n : ℕ) : Bits := BinaryLengthProgram.countWord n []
def squareWord (n : ℕ) : Bits := (mulCanonical (dimensionWord n) (dimensionWord n)).1
def fuelWord (n : ℕ) : Bits := (mulCanonical [true,true] (squareWord n)).1
def deltaValue (n : ℕ) : Fraction := (BinaryRational.div two (BinaryFractionalCore.naturalFraction (fuelWord n))).1

theorem countWord_increment (n : ℕ) (acc : Bits) :
    BinaryLengthProgram.countWord n (increment true acc).1=(increment true (BinaryLengthProgram.countWord n acc)).1 := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simpa only [BinaryLengthProgram.countWord] using ih (increment true acc).1

theorem dimension_lengthBits (xs : Bits) :
    dimensionWord xs.length=(BinaryCounters.lengthBits xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [dimensionWord,List.length_cons,BinaryLengthProgram.countWord,BinaryCounters.lengthBits]
    rw [countWord_increment]
    exact congrArg (fun a => (increment true a).1) ih

theorem dimension_value (n : ℕ) : value (dimensionWord n)=n := by
  simpa only [dimensionWord,value,Nat.zero_add] using (BinaryLengthProgram.countWord_spec n []).1

theorem dimension_width (n : ℕ) : (dimensionWord n).length≤n := by
  simpa only [dimensionWord,List.length_nil,Nat.zero_add] using (BinaryLengthProgram.countWord_spec n []).2

theorem parameters_exact (n : ℕ) :
    deltaValue n=(BinaryFractionalCore.parameters (dimensionWord n)).delta ∧
    fuelWord n=(BinaryFractionalCore.parameters (dimensionWord n)).fuel := by
  constructor <;> rfl

theorem input_parameters_exact {n : ℕ} (capacity : Row n) :
    deltaValue n=(BinaryFractionalCore.parameters (BinaryFractionalCore.dimension capacity).1).delta ∧
    fuelWord n=(BinaryFractionalCore.parameters (BinaryFractionalCore.dimension capacity).1).fuel := by
  have h := dimension_lengthBits (capacity.toList.map fun _ => false)
  simp only [List.length_map,Vector.length_toList] at h
  simpa only [BinaryFractionalCore.dimension,h] using parameters_exact n

theorem parameter_values (n : ℕ) :
    value (fuelWord n)=3*n^2 ∧ decode (deltaValue n)=FractionalCoverRawCore.deltaCode n := by
  have h := BinaryFractionalCore.parameters_spec (dimensionWord n)
  simpa only [←(parameters_exact n).1,←(parameters_exact n).2,dimension_value,FractionalCover.fuel] using h
end DirectedFlowCutGap.PackingParameters
