import DirectedFlowCutGap.BinaryMultiplicationProgram
import DirectedFlowCutGap.PackedWordPairTable

namespace DirectedFlowCutGap.BinaryMultiplicationSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace where
  state : BitState 96
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState 96 → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt BinaryMultiplicationProgram.program s
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

def check (name : String) (xs ys source : Bits) : IO Unit := do
  let l := PackedWordPairTable.word xs PackedWordPairTable.empty
  let r := PackedWordPairTable.word ys l
  let initial : BitState 96 :=
    ⟨r.heap,r.next,⟨l.root,r.root,[],[]⟩,[],94,source⟩
  let t := execute (BinaryMultiplicationProgram.steps xs ys+2) initial
  let heap := (eraseState t.state).heap
  let fuel := 2*xs.length+ys.length+4
  let result := observedList heap fuel (value t.state.registers.d)
  let oldLeft := observedList heap fuel (value l.root)
  let oldRight := observedList heap fuel (value r.root)
  unless t.halted && t.state.pc == 95 && t.state.stack.isEmpty &&
      t.state.source == source && result == some (mul xs ys).1 &&
      value (mul xs ys).1 == value xs*value ys &&
      oldLeft == some xs && oldRight == some ys && t.events.isEmpty &&
      t.state.heap.length == initial.heap.length+BinaryMultiplicationProgram.cells xs ys &&
      value t.state.next == t.state.heap.length &&
      t.operations ≤ completeBound 96 (initial.heap.length+1) (initial.heap.length+1)
        (BinaryMultiplicationProgram.steps xs ys+1) do
    throw (IO.userError ("FAILED binary multiplication fixture: "++name))
  IO.println ("PASS binary multiplication "++name)

end DirectedFlowCutGap.BinaryMultiplicationSmoke

open DirectedFlowCutGap.BinaryMultiplicationSmoke in
def main : IO Unit := do
  check "empty" [] [] [true,false]
  check "left-empty-padded" [] [true,true,false,false] [false,true]
  check "right-empty-padded" [false,true,false,false] [] [true,false]
  for x in [false,true] do
    for y in [false,true] do
      check (s!"bit-product-{x}-{y}") [x] [y] [true,false,true]
  check "unequal-all-ones" [true,true,true,true,true] [true,true] [false,true]
  check "two-padded-words" [true,false,false,false] [false,true,false] [true,false]
  check "alternating" [true,false,true,false] [false,true,false,true] []
  IO.println "PASS all10 binary multiplication execution fixtures"
