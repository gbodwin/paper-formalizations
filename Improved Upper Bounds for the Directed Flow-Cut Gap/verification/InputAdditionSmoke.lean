import DirectedFlowCutGap.InputAdditionProgram

namespace DirectedFlowCutGap.InputAdditionSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 84
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 84 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt InputAdditionProgram.program s
      match a.result with
      | none => ⟨s,[],a.operations,true⟩
      | some r =>
          let t := execute fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.halted⟩

/-- Test-only observation of the actual returned representation. -/
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

def check (name : String) (xs ys suffix : Bits) : IO Unit := do
  let source := SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++suffix
  let initial := InputAdditionProgram.initial source
  let t := execute (InputAdditionProgram.instructions xs ys+1) initial
  let heap := (eraseState t.state).heap
  let fuel := xs.length+ys.length+3
  let result := observedList heap fuel (value t.state.registers.d)
  let oldLeft := observedList heap fuel (value t.state.registers.a)
  let oldRight := observedList heap fuel (value t.state.registers.b)
  unless t.halted && t.state.pc == 63 && t.state.stack.isEmpty &&
      t.state.source == suffix && result == some (add false xs ys).1 &&
      value (add false xs ys).1 == value xs+value ys &&
      oldLeft == some xs && oldRight == some ys &&
      t.events == ((SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys).map Event.request) &&
      t.state.heap.length == 3*(xs.length+ys.length)+4+BinaryAdditionProgram.cells false xs ys &&
      value t.state.next == t.state.heap.length &&
      t.operations ≤ 15000000*(xs.length+ys.length+1)^3 do
    throw (IO.userError ("FAILED input addition fixture: "++name))
  IO.println ("PASS input addition "++name)

end DirectedFlowCutGap.InputAdditionSmoke

open DirectedFlowCutGap.InputAdditionSmoke in
def main : IO Unit := do
  check "empty" [] [] [true,false]
  check "left-empty-padded" [] [true,true,false,false] [false,true]
  check "right-empty-padded" [false,true,false,false] [] [true,false]
  for x in [false,true] do
    for y in [false,true] do
      check (s!"low-pair-{x}-{y}") [x] [y] [true,false,true]
  check "unequal-carry-chain" [true,true,true,true,true] [true] [false,true]
  check "two-padded-words" [true,false,false,false] [false,true,false] [true,false]
  check "long-carry-chain" (List.replicate 9 true) [true,false,false] [false,true,true]
  IO.println "PASS all10 input addition execution fixtures"
