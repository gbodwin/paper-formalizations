import DirectedFlowCutGap.ActualBinaryMaximum
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.BinaryMaximumSmoke
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


def check (name : String) (xs ys : Bits) (chooseRight : Bool) : IO Unit := do
  let l := PackedWordPairTable.word xs PackedWordPairTable.seed
  let r := PackedWordPairTable.word ys l
  let source := [false,true,false]
  let initial : BitState 56 := ⟨r.heap,r.next,⟨l.root,r.root,l.root,[]⟩,[],54,source⟩
  let old := (eraseState initial).heap
  let count := BinaryMaximumProgram.steps xs ys+1
  let actual := execute BinaryMaximumProgram.program (count+1) initial
  let final := eraseState actual.state
  let expected := if chooseRight then ys else xs
  let ptr := if chooseRight then value r.root else value l.root
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==55 && final.stack==[] && final.source==source && final.registers.d==ptr &&
      readBits final.heap (final.heap.length+1) final.registers.d==some expected &&
      readBits final.heap (final.heap.length+1) (value l.root)==some xs &&
      readBits final.heap (final.heap.length+1) (value r.root)==some ys &&
      final.heap.take old.length==old && final.heap.length==old.length+BinaryComparisonProgram.cells xs ys+1 &&
      actual.operations≤completeBound 56 (old.length+1) (old.length+1) (BinaryMaximumProgram.inputSteps xs ys) do
    throw (IO.userError ("FAIL actual binary maximum "++name))
  IO.println ("PASS actual binary maximum "++name++" steps="++toString actual.instructions)

def main : IO Unit := do
  check "empty-tie-right" [] [] true
  check "left-zero-padded" [false,false] [] true
  check "right-zero-padded" [] [false,false] true
  check "equal-padded-right" [true] [true,false,false] true
  check "left-greater" [false,true] [true] false
  check "right-greater" [true] [false,true] true
  check "left-padded-greater" [true,true,false] [false,true] false
  check "right-padded-greater" [true] [false,false,true,false] true
  check "both-padded-tie" [false,true,false] [false,true,false,false] true
  check "unequal-length-tie" [true,true,true] [true,true,true,false,false] true
  check "high-bit-left" [false,false,false,true] [true,true,true] false
  check "high-bit-right" [true,true,true] [false,false,false,true] true
end DirectedFlowCutGap.BinaryMaximumSmoke

def main : IO Unit := DirectedFlowCutGap.BinaryMaximumSmoke.main
