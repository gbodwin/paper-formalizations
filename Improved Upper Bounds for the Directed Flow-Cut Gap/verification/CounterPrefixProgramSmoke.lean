import DirectedFlowCutGap.PreparedCounterPrefix

namespace DirectedFlowCutGap.CounterPrefixProgramSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 24
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 24 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt CounterPrefixProgram.program s
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
  let init := PreparedCounterPrefix.initial word source
  let q := value word
  let r := execute (CounterPrefixProgram.steps word+1) init.1
  let observed := observedList (eraseState r.state).heap (q+1) (value r.state.registers.a)
  unless r.halted && r.state.pc == 22 && r.state.stack.isEmpty &&
      r.state.source == source.drop q &&
      observed == some (source.take q).reverse &&
      r.events == (source.take q).map Event.request &&
      r.state.heap.length == 2*word.length+3*q+3 &&
      value r.state.next == r.state.heap.length &&
      init.2+r.operations ≤ 2000000*(q+word.length+1)^3 do
    throw (IO.userError ("FAILED combined counter/source fixture: "++name))
  IO.println ("PASS combined counter/source "++name)

end DirectedFlowCutGap.CounterPrefixProgramSmoke

open DirectedFlowCutGap.CounterPrefixProgramSmoke in
def main : IO Unit := do
  check "empty-zero" [] [true,false]
  check "padded-zero" [false,false,false] [true,false]
  check "one-bit" [true] [false,true,true]
  check "five-padded" [true,false,true,false,false] [true,false,true,true,false,false,true]
  check "exact-prefix" [true,true] [false,true,false]
  IO.println "PASS all five combined counter/source execution fixtures"
