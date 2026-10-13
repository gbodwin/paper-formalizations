import DirectedFlowCutGap.ActualBinarySize
namespace DirectedFlowCutGap.BinarySizeSmoke
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


def check (name : String) (word expected : Bits) : IO Unit := do
  let prepared := PackedBooleanConstructor.construct word
  let source := [true,false,true]
  let initial : BitState 48 := ⟨prepared.heap,prepared.next,⟨prepared.root,[],[],[]⟩,[],46,source⟩
  let old := (eraseState initial).heap
  let count := BinarySizeProgram.steps word+1
  let actual := execute BinarySizeProgram.program (count+1) initial
  let final := eraseState actual.state
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==47 && final.stack==[] && final.source==source &&
      readBits final.heap (final.heap.length+1) final.registers.d==some expected &&
      readBits final.heap (final.heap.length+1) (eraseState initial).registers.a==some word &&
      final.heap.take old.length==old && final.heap.length==old.length+BinarySizeProgram.cells word &&
      actual.operations≤completeBound 48 old.length (2*word.length+2) (BinarySizeProgram.inputSteps word) do
    throw (IO.userError ("FAIL actual binary size "++name))
  IO.println ("PASS actual binary size "++name++" steps="++toString actual.instructions)

def main : IO Unit := do
  check "empty" [] []
  check "zero" [false] []
  check "padded-zero" [false,false,false,false] []
  check "one" [true] [true]
  check "padded-one" [true,false,false,false] [true]
  check "two" [false,true] [false,true]
  check "three" [true,true] [false,true]
  check "four" [false,false,true] [true,true]
  check "padded-five" [true,false,true,false,false] [true,true]
  check "seven-bits" [false,false,false,false,false,false,true] [true,true,true]
  check "eight-bits" [true,true,true,true,true,true,true,true] [false,false,false,true]
  check "nine-padded" [true,false,false,false,false,false,false,false,true,false,false] [true,false,false,true]
end DirectedFlowCutGap.BinarySizeSmoke

def main : IO Unit := DirectedFlowCutGap.BinarySizeSmoke.main
