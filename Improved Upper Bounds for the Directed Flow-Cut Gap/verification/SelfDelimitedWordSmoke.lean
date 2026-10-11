import DirectedFlowCutGap.SelfDelimitedWordProgram

namespace DirectedFlowCutGap.SelfDelimitedWordSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 10
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 10 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt SelfDelimitedWordProgram.program s
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

def check (name : String) (word suffix : Bits) : IO Unit := do
  let r := execute (6*word.length+6)
    (SelfDelimitedWordProgram.initial (SelfDelimitedWordProgram.encode word++suffix))
  let observed := observedList (eraseState r.state).heap (word.length+1)
    (value r.state.registers.d)
  unless r.halted && r.state.pc == 8 && r.state.stack.isEmpty &&
      r.state.source == suffix && observed == some word &&
      r.events == (SelfDelimitedWordProgram.encode word).map Event.request &&
      r.state.heap.length == 3*word.length+2 &&
      value r.state.next == r.state.heap.length &&
      r.operations ≤ 200000*(word.length+1)^3 do
    throw (IO.userError ("FAILED actual self-delimited word fixture: "++name))
  IO.println ("PASS actual self-delimited word "++name)

end DirectedFlowCutGap.SelfDelimitedWordSmoke

open DirectedFlowCutGap.SelfDelimitedWordSmoke in
def main : IO Unit := do
  check "empty" [] [true,false]
  check "zero-padding-preserved" [false,false,false,false] [true,false]
  check "mixed-bits" [true,false,true,false,true,false,true] [false,true,true]
  check "exact-encoded-prefix" [true,true,false,false,false,true,false,false] []
  IO.println "PASS all four actual self-delimited word execution fixtures"
