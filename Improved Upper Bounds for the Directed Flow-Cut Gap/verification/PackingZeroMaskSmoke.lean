import DirectedFlowCutGap.ActualPackingZeroMask
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PackingZeroMaskSmoke
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

def readFraction (heap : NaturalHeap) (p : ℕ) : Option (Bits×Bits) := do
  let some (.pair num den) := heap[p]? | none
  return (←readBits heap (heap.length+1) num,←readBits heap (heap.length+1) den)

def readRow (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits×Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair q rest) => do
      let value ← readFraction heap q
      return value::(←readRow heap fuel rest)
    | _ => none


def check (name : String) (rows : List (Bits×Bits)) (expected : Bits) : IO Unit := do
  let prep := PackedWordPairTable.construct rows
  let source := [true,false,true]
  let initial : BitState 32 := ⟨prep.heap,prep.next,⟨prep.root,prep.root,prep.root,prep.root⟩,[],30,source⟩
  let actual := execute PackingZeroMask.program (PackingZeroMask.steps rows+2) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let bound := 4*SourceRowTableProgram.bits rows+16*rows.length+4
  unless actual.halted && readBits heap (heap.length+1) regs.d==some expected &&
      readRow heap (heap.length+1) regs.a==some rows &&
      actual.instructions==PackingZeroMask.steps rows+1 && actual.instructions≤bound &&
      actual.operations≤completeBound 32 (prep.heap.length+1) (prep.heap.length+1) bound &&
      actual.state.pc==31 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==prep.heap.length+2*rows.length+1 do
    throw (IO.userError ("FAIL actual zero-mask "++name))
  IO.println ("PASS actual zero-mask "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "empty" [] []
  check "empty-zero" [([],[true])] [true]
  check "padded-zero" [([false,false,false],[true,false])] [true]
  check "one" [([true],[true])] [false]
  check "delayed-one" [([false,false,true,false],[false,true])] [false]
  check "ordered-mixed" [([],[true]),([true,false],[true]),([false,false],[true]),([false,true],[true])] [true,false,true,false]
  check "raw-zero-denominators" [([true],[]),([],[false,false])] [false,true]
  check "duplicates" (List.replicate 6 ([false,false],[true,false])) (List.replicate 6 true)
end DirectedFlowCutGap.PackingZeroMaskSmoke

def main := DirectedFlowCutGap.PackingZeroMaskSmoke.main
