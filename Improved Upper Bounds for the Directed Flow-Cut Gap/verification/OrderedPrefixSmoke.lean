import DirectedFlowCutGap.PreparedOrderedCounterPrefix

namespace DirectedFlowCutGap.OrderedPrefixSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 30
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 30 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt OrderedCounterPrefix.program s
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
  let init := PreparedOrderedCounterPrefix.initial word source
  let q := value word
  let r := execute (OrderedCounterPrefix.steps word+1) init.1
  let observed := observedList (eraseState r.state).heap (q+1) (value r.state.registers.b)
  unless r.halted && r.state.pc == 29 && r.state.stack.isEmpty &&
      r.state.source == source.drop q &&
      observed == some (source.take q) &&
      r.events == (source.take q).map Event.request &&
      r.state.heap.length == 2*word.length+4*q+4 &&
      value r.state.next == r.state.heap.length &&
      init.2+r.operations ≤ 2000000*(q+word.length+1)^3 do
    throw (IO.userError ("FAILED ordered counter/source fixture: "++name))
  IO.println ("PASS ordered counter/source "++name)

end DirectedFlowCutGap.OrderedPrefixSmoke

open DirectedFlowCutGap.OrderedPrefixSmoke in
def main : IO Unit := do
  check "empty-zero" [] [true,false]
  check "padded-zero" [false,false,false] [true,false]
  check "one-bit" [true] [false,true,true]
  check "five-padded" [true,false,true,false,false] [true,false,true,true,false,false,true]
  check "exact-prefix" [true,true] [false,true,false]
  IO.println "PASS all five ordered counter/source execution fixtures"
