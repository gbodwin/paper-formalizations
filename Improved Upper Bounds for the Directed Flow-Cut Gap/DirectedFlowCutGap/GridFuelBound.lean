import DirectedFlowCutGap.GridFuelTrace
import DirectedFlowCutGap.FractionWidthExecution

namespace DirectedFlowCutGap.GridFuelProgram
open BinaryArithmetic

theorem canonical_mul_length (xs ys : Bits) :
    (mulCanonical xs ys).1.length ≤ 2*xs.length+ys.length+1 := by
  exact ((trim_spec (mul xs ys).1).2.2.1).trans (mul_spec xs ys).2.1

theorem canonical_add_length (xs ys : Bits) :
    (addCanonical xs ys).1.length ≤ xs.length+ys.length+1 := by
  have h := ((trim_spec (add false xs ys).1).2.2.1).trans (add_spec false xs ys).2.1
  change (addCanonical xs ys).1.length ≤ _ at h
  have hm : max xs.length ys.length ≤ xs.length+ys.length := by omega
  omega

def inputSteps (dimension width : Bits) : ℕ := 900*(dimension.length+width.length+15)^2

theorem steps_bound (dimension width : Bits) : steps dimension width+1 ≤ inputSteps dimension width := by
  let S := dimension.length+width.length+15
  let size := (BinaryCounters.sizeBits dimension).1
  let tw := (mulCanonical [false,true] width).1
  let tn := (mulCanonical [false,true] size).1
  let sum := (addCanonical tw tn).1
  have hs : size.length ≤ dimension.length := FractionWidthProgram.size_length dimension
  have hw : tw.length ≤ width.length+5 := by
    have h := canonical_mul_length [false,true] width
    simpa [tw,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
  have hn : tn.length ≤ dimension.length+5 := by
    have h := canonical_mul_length [false,true] size
    simp only [List.length_cons,List.length_nil] at h
    change tn.length ≤ _ at h
    omega
  have hm : sum.length ≤ dimension.length+width.length+11 := by
    have h := canonical_add_length tw tn
    change sum.length ≤ _ at h
    omega
  have bound (p : Bool) (a b : Bits) (h : a.length+b.length+2 ≤ S) :
      CanonicalArithmeticProgram.instructions p a b ≤ 200*S^2 :=
    (CanonicalArithmeticProgram.instructions_bound p a b).trans
      (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left h 2))
  have b1 := bound true [false,true] width (by simp only [List.length_cons,List.length_nil];dsimp [S];omega)
  have b2 := bound true [false,true] size (by simp only [List.length_cons,List.length_nil];dsimp [S];omega)
  have b3 := bound false tw tn (by dsimp [S];omega)
  have b4 := bound false sum [true,true] (by simp only [List.length_cons,List.length_nil];dsimp [S];omega)
  have b0 : BinarySizeProgram.steps dimension+1 ≤ 32*S^2 :=
    (BinarySizeProgram.steps_bound dimension).trans
      (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (show dimension.length+1 ≤ S by dsimp [S];omega) 2))
  have positive : 1≤S := by dsimp [S];omega
  change BinarySizeProgram.steps dimension+CanonicalArithmeticProgram.instructions true [false,true] width+
    CanonicalArithmeticProgram.instructions true [false,true] size+
    CanonicalArithmeticProgram.instructions false tw tn+
    CanonicalArithmeticProgram.instructions false sum [true,true]+28+1 ≤ 900*S^2
  nlinarith
end DirectedFlowCutGap.GridFuelProgram
