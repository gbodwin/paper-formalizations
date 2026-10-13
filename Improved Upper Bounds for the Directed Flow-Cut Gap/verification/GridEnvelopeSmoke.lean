import DirectedFlowCutGap.GridFamilyEnvelope

/-! Numerical-envelope checks only. These do not execute a physical machine. -/
namespace DirectedFlowCutGap.GridEnvelopeSmoke
open BinaryArithmetic BinaryRational GridFamilyEnvelope

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def paddedZero : Fraction := ⟨[false,false,false],[true,false,false],by decide⟩
def paddedHalf : Fraction := ⟨[true,false,false],[false,true,false],by decide⟩

def checkInput (name : String) (d : ℕ) (rows : List Fraction) : IO Unit := do
  let S := LambdaRowProgram.rowBits rows
  let W := wordBound rows.length S
  let fuel := GridFamilyInput.fuel rows
  let old := GridFamilyInput.inputSteps d rows
  let bound := instructionBound d rows.length S
  unless fuel.length≤W && value fuel≤W && value fuel==LambdaGridProgram.gridLimit rows &&
      GridInputProgram.inputSteps rows==prefixBound rows.length S &&
      OriginalRowMinimum.inputSteps rows==minimumBound rows.length S && old≤bound do
    throw (IO.userError ("FAILED numerical original-input envelope "++name))
  IO.println ("PASS numerical original-input envelope "++name++" grid-length="++toString (value fuel))

def checkController (name : String) (d : ℕ) (rows : List Fraction) (exp fuel : Bits) (W : ℕ) : IO Unit := do
  let L := LambdaGridProgram.gridLimit rows
  unless value exp+value fuel≤L && exp.length+value fuel≤W && fuel.length≤W do
    throw (IO.userError ("BAD fixture controller preconditions "++name))
  unless GridFamily.instructionBound d rows exp fuel≤
      (value fuel+1)*bodyBound d rows.length (LambdaRowProgram.rowBits rows) W do
    throw (IO.userError ("FAILED numerical recursive envelope "++name))
  let mut e := exp
  let mut f := fuel
  for _ in List.range (value fuel+1) do
    unless value e+value f≤L && e.length+value f≤W && f.length≤W do
      throw (IO.userError ("FAILED conserved controller invariant "++name))
    unless (isZero f).1 do
      e := (increment true e).1
      f := (predecessor f).1
  unless value f==0 do throw (IO.userError ("FAILED controller termination "++name))
  IO.println ("PASS numerical controller envelope "++name)

def main : IO Unit := do
  checkInput "empty" 0 []
  checkInput "zero" 0 [zero]
  checkInput "padded-zero" 1 [paddedZero]
  checkInput "one" 0 [one]
  checkInput "one-demand" 1 [one]
  checkInput "half-padded" 1 [paddedHalf]
  checkInput "mixed" 3 [paddedZero,frac 5 2,one]
  checkInput "four-rationals" 7 [frac 31 7,frac 8 4,paddedHalf,frac 0 9]
  checkController "zero-fuel-padded" 1 [one] [] [false,false,false,false] 30
  checkController "padded-positive-fuel" 2 [paddedHalf] [] ((GridFamilyInput.fuel [paddedHalf])++[false,false,false]) 40
  checkController "nonzero-exponent-padded" 2 [paddedHalf] [true,false,false] [true,false,true,false] 40
  checkController "last-singleton" 2 [one] (LambdaGridProgram.gridLimit [one]-1).bits [true,false,false] 40
end DirectedFlowCutGap.GridEnvelopeSmoke

def main := DirectedFlowCutGap.GridEnvelopeSmoke.main
