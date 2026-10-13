import DirectedFlowCutGap.ActualBinaryPredecessor
namespace DirectedFlowCutGap.BinaryPredecessorSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
structure Trace where
  state : BitState 64
  events : List Event
  operations : ℕ
  instructions : ℕ
  halted : Bool

def execute : ℕ → BitState 64 → Trace
  | 0,s => ⟨s,[],0,0,false⟩
  | fuel+1,s =>
      let a := attempt BinaryPredecessorProgram.program s
      match a.result with
      | none => ⟨s,[],a.operations,0,true⟩
      | some r =>
          let t := execute fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.instructions+1,t.halted⟩

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none

def check (name : String) (word expected : Bits) : IO Unit := do
  let prepared := construct word
  let source := [true,false,true]
  let initial : BitState 64 := ⟨prepared.heap,prepared.next,⟨prepared.root,prepared.root,prepared.root,[]⟩,[],62,source⟩
  let old := (eraseState initial).heap
  let count := BinaryPredecessorProgram.steps word+1
  let actual := execute (count+1) initial
  let final := eraseState actual.state
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==63 && final.stack==[] && final.source==source &&
      final.registers.a==value prepared.root && final.registers.b==value prepared.root && final.registers.c==value prepared.root &&
      readBits final.heap (final.heap.length+1) final.registers.d==some expected &&
      readBits final.heap (final.heap.length+1) (value prepared.root)==some word &&
      final.heap.take old.length==old && final.heap.length==old.length+BinaryPredecessorProgram.cells word &&
      value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 64 (old.length+1) (old.length+1) (BinaryPredecessorProgram.inputSteps word) do
    throw (IO.userError ("FAIL actual predecessor "++name))
  IO.println ("PASS actual predecessor "++name++" steps="++toString actual.instructions)

def main : IO Unit := do
  check "empty" [] []
  check "zero" [false] []
  check "one" [true] []
  check "double-zero" [false,false] []
  check "two" [false,true] [true]
  check "padded-one" [true,false,false] []
  check "four" [false,false,true] [true,true]
  check "eight" [false,false,false,true] [true,true,true]
  check "all-ones" [true,true,true] [false,true,true]
  check "padded-two" [false,true,false,false] [true]
  check "all-zero-eight" [false,false,false,false,false,false,false,false] []
  check "full-borrow" [false,false,false,false,false,false,false,false,true] [true,true,true,true,true,true,true,true]
end DirectedFlowCutGap.BinaryPredecessorSmoke

def main : IO Unit := DirectedFlowCutGap.BinaryPredecessorSmoke.main
