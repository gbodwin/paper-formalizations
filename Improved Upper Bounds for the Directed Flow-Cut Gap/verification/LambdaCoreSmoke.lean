import DirectedFlowCutGap.ActualLambdaCore
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.LambdaCoreSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  instructions : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) (fuel : ℕ) (s : BitState C) : Trace C :=
  go fuel s [] 0 0
where
  go : ℕ → BitState C → List Event → ℕ → ℕ → Trace C
  | 0,s,events,operations,instructions => ⟨s,events.reverse,operations,instructions,false⟩
  | fuel+1,s,events,operations,instructions =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,events.reverse,operations+a.operations,instructions,true⟩
      | some r => go fuel r.state (r.events.reverse++events) (operations+a.operations) (instructions+1)

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none


def readFraction (heap : NaturalHeap) (root : ℕ) : Option (Bits × Bits) := do
  let .pair n d ← heap[root]? | none
  return (← readBits heap (heap.length+1) n,← readBits heap (heap.length+1) d)

def check (name : String) (num den dimension exponent wantNum wantDen : Bits) : IO Unit := do
  if hd : 0<value den then
    let x : BinaryRational.Fraction := ⟨num,den,hd⟩
    let n := PackedWordPairTable.word num PackedWordPairTable.seed
    let d := PackedWordPairTable.word den n
    let r := PackedWordPairTable.allocate (.pair n.root d.root) d
    let dim := PackedWordPairTable.word dimension r
    let exp := PackedWordPairTable.word exponent dim
    let source := [false,true,false]
    let initial : BitState 432 := ⟨exp.heap,exp.next,⟨r.root,dim.root,exp.root,[]⟩,[],430,source⟩
    let old := (eraseState initial).heap
    let count := LambdaCoreProgram.steps x dimension exponent+1
    let actual := execute LambdaCoreProgram.program (count+1) initial
    let final := eraseState actual.state
    unless actual.halted && actual.instructions==count && actual.events==[] &&
        final.pc==431 && final.stack==[] && final.source==source &&
        readFraction final.heap final.registers.d==some (wantNum,wantDen) &&
        readFraction final.heap (value r.root)==some (num,den) &&
        readBits final.heap (final.heap.length+1) (value dim.root)==some dimension &&
        readBits final.heap (final.heap.length+1) (value exp.root)==some exponent &&
        final.registers.a==value r.root && final.registers.b==value dim.root && final.registers.c==value exp.root &&
        final.heap.take old.length==old && final.heap.length==old.length+LambdaCoreProgram.cells x dimension exponent &&
        value actual.state.next==actual.state.heap.length &&
        actual.operations≤completeBound 432 (old.length+1) (old.length+1) (LambdaCoreProgram.inputSteps x dimension exponent) do
      throw (IO.userError ("FAIL actual lambda "++name++s!" result={readFraction final.heap final.registers.d}"))
    IO.println ("PASS actual lambda "++name++" steps="++toString actual.instructions)
  else throw (IO.userError "invalid fixture denominator")

def main (args : List String) : IO Unit := do
  match args.head?.getD "small" with
  | "small" =>
    check "zero-dimension" [] [true] [] [] [] [true]
    check "nonzero-zero-dimension" [true,true] [false,true] [] [] [] [true]
    check "zero-cost" [] [true] [true] [] [] [true]
  | "middle" =>
    check "one" [true] [true] [true] [] [true] [true]
    check "half" [true] [true] [false,true] [] [true] [false,true]
    check "padded-one" [true,false] [true,false] [true,false] [false,false] [true] [true]
  | "powers" =>
    check "power-one" [true] [true] [true] [true] [false,true] [true]
    check "power-two-half" [true] [true] [false,true] [false,true] [false,false,true] [false,true]
    check "fraction" [false,true] [true,true] [false,true] [true] [false,false,true] [false,true,true]
  | _ =>
    check "unreduced" [false,false,true] [false,true] [false,true] [] [false,false,true] [false,false,true]
    check "zero-dimension-power" [true] [true] [false,false] [false,true] [] [true]
    check "padded-fraction" [false,true,false] [true,true,false] [true,true,false] [false,true,false] [false,false,false,true] [true,false,false,true]
end DirectedFlowCutGap.LambdaCoreSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.LambdaCoreSmoke.main args
