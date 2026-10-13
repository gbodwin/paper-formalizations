import DirectedFlowCutGap.BinaryBorrowProgram
namespace DirectedFlowCutGap.BinaryBorrowSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
structure Trace where
  state : BitState 16
  events : List Event
  operations : ℕ
  instructions : ℕ
  halted : Bool

def execute : ℕ → BitState 16 → Trace
  | 0,s => ⟨s,[],0,0,false⟩
  | fuel+1,s =>
      let a := attempt BinaryBorrowProgram.program s
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
  let initial : BitState 16 := ⟨prepared.heap,prepared.next,⟨prepared.root,prepared.root,prepared.root,[]⟩,[],15,source⟩
  let old := (eraseState initial).heap
  let count := BinaryBorrowProgram.steps word+1
  let actual := execute (count+1) initial
  let final := eraseState actual.state
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==14 && final.stack==[] && final.source==source &&
      final.registers.a==value prepared.root && final.registers.b==value prepared.root && final.registers.c==value prepared.root &&
      readBits final.heap (final.heap.length+1) final.registers.d==some expected &&
      readBits final.heap (final.heap.length+1) (value prepared.root)==some word &&
      final.heap.take old.length==old && final.heap.length==old.length+BinaryBorrowProgram.cells word &&
      value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 16 (old.length+1) (old.length+1) count do
    throw (IO.userError ("FAIL actual borrow "++name))
  IO.println ("PASS actual borrow "++name++" steps="++toString actual.instructions)

def main : IO Unit := do
  check "empty" [] []
  check "zero" [false] [true]
  check "one" [true] [false]
  check "double-zero" [false,false] [true,true]
  check "two" [false,true] [true,false]
  check "padded-one" [true,false,false] [false,false,false]
  check "four" [false,false,true] [true,true,false]
  check "eight" [false,false,false,true] [true,true,true,false]
  check "all-ones" [true,true,true] [false,true,true]
  check "padded-two" [false,true,false,false] [true,false,false,false]
  check "all-zero-eight" [false,false,false,false,false,false,false,false] [true,true,true,true,true,true,true,true]
  check "full-borrow" [false,false,false,false,false,false,false,false,true] [true,true,true,true,true,true,true,true,false]
end DirectedFlowCutGap.BinaryBorrowSmoke

def main : IO Unit := DirectedFlowCutGap.BinaryBorrowSmoke.main
