import DirectedFlowCutGap.PreparedBinaryIncrement

namespace DirectedFlowCutGap.PreparedIncrementSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 16
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 16 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt BinaryIncrementProgram.program s
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
  let init := PreparedBinaryIncrement.initial word source
  let r := execute (BinaryIncrementProgram.steps word+2) init.1
  let observed := observedList (eraseState r.state).heap (word.length+2)
    (value r.state.registers.d)
  let old := observedList (eraseState r.state).heap (word.length+1)
    (value init.1.registers.a)
  unless r.halted && r.state.pc == 14 && r.state.stack.isEmpty &&
      r.state.source == source && observed == some (increment true word).1 &&
      old == some word && r.events.isEmpty &&
      r.state.heap.length == 2*word.length+1+BinaryIncrementProgram.cells word &&
      value r.state.next == r.state.heap.length &&
      init.2+r.operations ≤ 1000000*(word.length+1)^3 do
    throw (IO.userError ("FAILED prepared binary increment fixture: "++name))
  IO.println ("PASS prepared binary increment "++name)

end DirectedFlowCutGap.PreparedIncrementSmoke

open DirectedFlowCutGap.PreparedIncrementSmoke in
def main : IO Unit := do
  check "empty-zero" [] [true,false]
  check "false-head-tail-sharing" [false,true,false] [true,false]
  check "full-carry" [true,true,true] [false,true,true]
  check "high-zero-padding" [true,true,false,false,false] [true,false]
  IO.println "PASS all four prepared binary increment execution fixtures"
