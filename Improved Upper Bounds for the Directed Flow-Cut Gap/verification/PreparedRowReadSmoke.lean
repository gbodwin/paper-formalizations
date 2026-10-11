import DirectedFlowCutGap.PreparedIndexedPairRead

namespace DirectedFlowCutGap.PreparedRowReadSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 26
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 26 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt BinaryIndexedPairRead.program s
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


def check (name : String) (rows : List (Bits × Bits)) (word source : Bits) : IO Unit := do
  let init := PreparedIndexedPairRead.initial rows word source
  let q := value word
  let r := execute (BinaryIndexedPairRead.steps word+1) init.1
  let heap := (eraseState r.state).heap
  let num := observedList heap (heap.length+1) (value r.state.registers.a)
  let den := observedList heap (heap.length+1) (value r.state.registers.b)
  let row := rows[q]?
  unless r.halted && r.state.pc == 24 && r.state.stack.isEmpty &&
      r.state.source == source && r.events.isEmpty &&
      num == row.map Prod.fst && den == row.map Prod.snd &&
      r.state.heap.length == init.1.heap.length+q+1 &&
      value r.state.next == r.state.heap.length &&
      init.2+r.operations ≤ 3000000*(PreparedIndexedPairRead.inputSize rows word)^3 do
    throw (IO.userError ("FAILED constructed rational-row read fixture: "++name))
  IO.println ("PASS constructed rational-row read "++name)

end DirectedFlowCutGap.PreparedRowReadSmoke

open DirectedFlowCutGap.PreparedRowReadSmoke in
def main : IO Unit := do
  check "empty-fields-zero-index" [([],[])] [] [true,false]
  check "padded-fields-and-index" [([true,false,false],[false,true,false]),([],[])]
    [false,false,false] [true,false]
  check "second-record" [([true],[true]),([false,false],[true,true,false]),([false],[true])]
    [true,false,false] [false,true,false]
  check "third-record" [([],[]),([true],[false]),([true,false,true,false],[false,true,false,false])]
    [false,true,false] [true,true]
  IO.println "PASS all four constructed rational-row read execution fixtures"
