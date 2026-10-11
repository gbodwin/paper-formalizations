import DirectedFlowCutGap.PreparedBinaryLength

namespace DirectedFlowCutGap.BinaryLengthSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 24
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 24 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt BinaryLengthProgram.program s
      match a.result with
      | none => ⟨s,[],a.operations,true⟩
      | some r =>
          let t := execute fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.halted⟩

/-- Test observation only: no natural-indexed decoder is substituted into the
certified program or its operation bound. -/
def observedList (heap : NaturalHeap) : ℕ → ℕ → Option (List Bool)
  | 0,_ => none
  | fuel+1,root =>
      match heap[root]? with
      | some .nil => some []
      | some (.pair head tail) =>
          match heap[head]?, observedList heap fuel tail with
          | some (.flag b),some bs => some (b::bs)
          | _,_ => none
      | _ => none

def check (name : String) (word source : Bits) : IO Unit := do
  let init := PreparedBinaryLength.initial word source
  let r := execute (2+BinaryLengthProgram.scanSteps word.length []) init.1
  let observed := observedList (eraseState r.state).heap (word.length+1)
    (value r.state.registers.b)
  let old := observedList (eraseState r.state).heap (word.length+1)
    (value init.1.registers.a)
  unless r.halted && r.state.pc == 22 && r.state.stack.isEmpty &&
      r.state.source == source && observed == some (BinaryLengthProgram.countWord word.length []) &&
      (observed.map value) == some word.length && old == some word && r.events.isEmpty &&
      r.state.heap.length == 2*word.length+2+BinaryLengthProgram.scanCells word.length [] &&
      value r.state.next == r.state.heap.length &&
      init.2+r.operations ≤ 15000000*(word.length+1)^6 do
    throw (IO.userError ("FAILED actual binary length fixture: "++name))
  IO.println ("PASS actual binary length "++name)

end DirectedFlowCutGap.BinaryLengthSmoke

open DirectedFlowCutGap.BinaryLengthSmoke in
def main : IO Unit := do
  check "empty" [] [true,false]
  check "zero-padding-counted" [false,false,false,false] [true,false]
  check "seven-and-carries" [true,false,true,false,true,false,true] [false,true,true]
  check "eight-power-of-two" [true,true,false,false,false,true,false,false] [true,false]
  IO.println "PASS all four actual binary length execution fixtures"
