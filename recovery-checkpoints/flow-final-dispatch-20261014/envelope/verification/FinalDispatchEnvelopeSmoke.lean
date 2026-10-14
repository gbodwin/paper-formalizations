import DirectedFlowCutGap.FinalDispatchEnvelope

/-!
Numerical regressions only: these evaluate input-cost expressions and stored
word lengths. No physical interpreter, heap fixture, branch trace, or measured
physical charge is executed or claimed here.
-/
namespace DirectedFlowCutGap.FinalDispatchEnvelopeSmoke
open BinaryArithmetic BinaryRational FinalDispatchEnvelope

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def paddedZero : Fraction := ⟨[false,false,false],[true,false,false],by decide⟩
def paddedHalf : Fraction := ⟨[true,false,false],[false,true,false],by decide⟩

def emptyBound (N : ℕ) : ℕ := 26*(N+N+1)+6*N+6*(N*N)+40

def avoidingBound (N : ℕ) : ℕ :=
  (4*N+16*N+(32*(N*N)+(32*(N+N+2)+25)*N+4)+18)+
    (24*(N*N)+28*N+4)+11+
    (5*N+49+GraphRecoveryController.instructionBound N (N+1) N)+11

def dispatchBound (N : ℕ) : ℕ :=
  N*(emptyBound N+12)+4+(N*(avoidingBound N+20)+4)+4*N+16*N+25

def checkInput {n : ℕ} (name : String) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (H B : ℕ) : IO Unit := do
  let S := LambdaRowProgram.rowBits costs.toList
  let N := ds.length+n+S+H+B+1
  let vs := List.ofFn (RowVertices.vertexLabel (n:=n))
  let cs := IndexedRationalRead.fields costs.toList
  let rows := GraphRelaxationRefinement.matrix adjacency
  let demands := ds.map fun e => (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2)
  let dispatch := OriginalDispatch.inputSteps vs cs rows demands (n+1)
  let original := RowVertices.instructionBound n+dispatch+
    OriginalRowMinimum.inputSteps costs.toList+
    GridFamilyEnvelope.instructionBound ds.length n S+32
  let diagonal := RowVertices.instructionBound N+dispatchBound N+
    GridFamilyEnvelope.minimumBound N N+GridFamilyEnvelope.instructionBound N N N+32
  unless SourceRowTableProgram.bits cs==S && cs.length==n && vs.length==n &&
      (vs.map List.length).sum≤N*N && (rows.map List.length).sum==n*n &&
      dispatch≤dispatchBound N && original≤diagonal &&
      FinalDispatch.inputBound adjacency costs ds==original do
    throw (IO.userError ("FAILED numerical final-dispatch envelope "++name))
  IO.println ("PASS numerical final-dispatch envelope "++name++
    " occurrences="++toString ds.length++" stored-cost-bits="++toString S++
    " measure="++toString N)

def adjacency (n : ℕ) (edge : Fin n → Fin n → Bool) : BinaryFractionalWalkOracle.Adjacency n :=
  Vector.ofFn fun i => Vector.ofFn fun j => edge i j

def main : IO Unit := do
  checkInput "empty" (adjacency 0 fun _ _ => false) (Vector.ofFn fun _ => one) [] 0 0
  checkInput "singleton-no-demands" (adjacency 1 fun _ _ => false)
    (Vector.ofFn fun _ => one) [] 0 0
  checkInput "singleton-self-demand" (adjacency 1 fun _ _ => false)
    (Vector.ofFn fun _ => one) [(0,0)] 3 5
  checkInput "padded-zero-repeated-demands" (adjacency 2 fun _ _ => false)
    (Vector.ofFn fun _ => paddedZero) [(0,1),(0,1),(1,0)] 7 9
  checkInput "padded-half-dense" (adjacency 2 fun _ _ => true)
    (Vector.ofFn fun _ => paddedHalf) [(0,1),(1,0)] 4 3
  checkInput "mixed-sparse" (adjacency 3 fun i j => decide (i.val+1=j.val))
    (Vector.ofFn fun i => if i.val=0 then paddedZero else if i.val=1 then frac 5 2 else one)
    [(0,2),(2,0),(0,2),(1,2)] 11 4
  checkInput "four-rationals" (adjacency 4 fun i j => decide (i≠j))
    (Vector.ofFn fun i => frac (i.val*7+1) (i.val+1)) [(0,3),(3,0),(1,2)] 2 6

end DirectedFlowCutGap.FinalDispatchEnvelopeSmoke

#eval DirectedFlowCutGap.FinalDispatchEnvelopeSmoke.main
