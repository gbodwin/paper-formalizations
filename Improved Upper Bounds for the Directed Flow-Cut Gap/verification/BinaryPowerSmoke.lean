import DirectedFlowCutGap.ActualBinaryPower
namespace DirectedFlowCutGap.BinaryPowerSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
structure Trace where
  state : BitState 96
  events : List Event
  operations : ℕ
  instructions : ℕ
  halted : Bool

def execute : ℕ → BitState 96 → Trace
  | 0,s => ⟨s,[],0,0,false⟩
  | fuel+1,s =>
      let a := attempt BinaryPowerProgram.program s
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
  let initial : BitState 96 := ⟨prepared.heap,prepared.next,⟨prepared.root,prepared.root,prepared.root,[]⟩,[],94,source⟩
  let old := (eraseState initial).heap
  let count := BinaryPowerProgram.steps word+1
  let actual := execute (count+1) initial
  let final := eraseState actual.state
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==95 && final.stack==[] && final.source==source &&
      final.registers.a==value prepared.root && final.registers.b==value prepared.root && final.registers.c==value prepared.root &&
      readBits final.heap (final.heap.length+1) final.registers.d==some expected &&
      readBits final.heap (final.heap.length+1) (value prepared.root)==some word &&
      final.heap.take old.length==old && final.heap.length==old.length+BinaryPowerProgram.cells word &&
      value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 96 (old.length+1) (old.length+1) (BinaryPowerProgram.inputSteps word) do
    throw (IO.userError ("FAIL actual binary power "++name))
  IO.println ("PASS actual binary power "++name++" steps="++toString actual.instructions)

def main (args : List String) : IO Unit := do
  if args==["larger"] then
    check "four" [false,false,true] [false,false,false,false,true]
    check "padded-four" [false,false,true,false,false] [false,false,false,false,true]
    check "five" [true,false,true] [false,false,false,false,false,true]
    check "seven" [true,true,true] (List.replicate 7 false++[true])
    check "eight" [false,false,false,true] (List.replicate 8 false++[true])
    check "sixteen" [false,false,false,false,true] (List.replicate 16 false++[true])
  else
    check "empty" [] [true]
    check "zero" [false] [true]
    check "padded-zero" [false,false,false] [true]
    check "one" [true] [false,true]
    check "padded-one" [true,false,false] [false,true]
    check "three" [true,true] [false,false,false,true]
end DirectedFlowCutGap.BinaryPowerSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.BinaryPowerSmoke.main args
