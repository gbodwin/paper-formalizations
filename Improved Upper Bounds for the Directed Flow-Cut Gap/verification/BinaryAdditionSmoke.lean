import DirectedFlowCutGap.BinaryAdditionProgram
import DirectedFlowCutGap.PackedWordPairTable

namespace DirectedFlowCutGap.BinaryAdditionSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 64
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 64 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt BinaryAdditionProgram.program s
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

def check (name : String) (carry : Bool) (xs ys source : Bits) : IO Unit := do
  let l := PackedWordPairTable.word xs PackedWordPairTable.empty
  let r := PackedWordPairTable.word ys l
  let initial : BitState 64 :=
    ⟨r.heap,r.next,⟨l.root,r.root,[],[]⟩,[],BinaryAdditionProgram.topEntry carry,source⟩
  let t := execute (BinaryAdditionProgram.steps carry xs ys+2) initial
  let heap := (eraseState t.state).heap
  let fuel := xs.length+ys.length+3
  let result := observedList heap fuel (value t.state.registers.d)
  let oldLeft := observedList heap fuel (value l.root)
  let oldRight := observedList heap fuel (value r.root)
  unless t.halted && t.state.pc == 63 && t.state.stack.isEmpty &&
      t.state.source == source && result == some (add carry xs ys).1 &&
      value (add carry xs ys).1 == value xs+value ys+carry.toNat &&
      oldLeft == some xs && oldRight == some ys && t.events.isEmpty &&
      t.state.heap.length == initial.heap.length+BinaryAdditionProgram.cells carry xs ys &&
      value t.state.next == t.state.heap.length &&
      t.operations ≤ completeBound 64 (initial.heap.length+1) (initial.heap.length+1)
        (BinaryAdditionProgram.steps carry xs ys+1) do
    throw (IO.userError ("FAILED binary addition fixture: "++name))
  IO.println ("PASS binary addition "++name)

end DirectedFlowCutGap.BinaryAdditionSmoke

open DirectedFlowCutGap.BinaryAdditionSmoke in
def main : IO Unit := do
  check "empty-no-carry" false [] [] [true,false]
  check "empty-carry" true [] [] [false,true]
  check "left-empty-padded" true [] [true,true,false,false] [false,true]
  check "right-empty-padded" false [false,true,false,false] [] [true,false]
  for c in [false,true] do
    for x in [false,true] do
      for y in [false,true] do
        check (s!"full-adder-{c}-{x}-{y}") c [x] [y] [true,false,true]
  check "unequal-carry-chain" false [true,true,true,true,true] [true] [false,true]
  check "two-padded-words" true [true,false,false,false] [false,true,false] [true,false]
  IO.println "PASS all14 binary addition execution fixtures"
