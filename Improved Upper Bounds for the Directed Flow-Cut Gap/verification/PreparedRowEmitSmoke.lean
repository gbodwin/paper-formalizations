import DirectedFlowCutGap.PreparedRowEmit

namespace DirectedFlowCutGap.PreparedRowEmitSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 36
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 36 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt IndexedPairEmit.program s
      match a.result with
      | none => ⟨s,[],a.operations,true⟩
      | some r =>
          let t := execute fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.halted⟩


def check (name : String) (rows : List (Bits × Bits)) (word source : Bits) : IO Unit := do
  let init := PreparedRowEmit.initial rows word source
  let q := value word
  let row := rows[q]!
  let r := execute (IndexedPairEmit.steps word row.1 row.2+1) init.1
  unless r.halted && r.state.pc == 35 && r.state.stack.isEmpty &&
      r.state.source == source && r.events == (row.1++row.2).map Event.emit &&
      r.state.heap.length == init.1.heap.length+q+1 &&
      value r.state.next == r.state.heap.length &&
      init.2+r.operations ≤ 10000000*(PreparedIndexedPairRead.inputSize rows word)^3 do
    throw (IO.userError ("FAILED constructed rational-row emitted output fixture: "++name))
  IO.println ("PASS constructed rational-row emitted output "++name)

end DirectedFlowCutGap.PreparedRowEmitSmoke

open DirectedFlowCutGap.PreparedRowEmitSmoke in
def main : IO Unit := do
  check "empty-fields-zero-index" [([],[])] [] [true,false]
  check "padded-fields-and-index" [([true,false,false],[false,true,false]),([],[])]
    [false,false,false] [true,false]
  check "second-record" [([true],[true]),([false,false],[true,true,false]),([false],[true])]
    [true,false,false] [false,true,false]
  check "third-record" [([],[]),([true],[false]),([true,false,true,false],[false,true,false,false])]
    [false,true,false] [true,true]
  IO.println "PASS all four constructed rational-row emitted output execution fixtures"
