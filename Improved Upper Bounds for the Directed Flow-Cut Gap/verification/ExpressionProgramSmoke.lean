import DirectedFlowCutGap.PackingBudgetProgram
import DirectedFlowCutGap.PackedWordPairTable

namespace DirectedFlowCutGap.ExpressionProgramSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open ConcreteExpressionProgram

structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) : ℕ → BitState C → Trace C
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,[],a.operations,true⟩
      | some r =>
          let t := execute p fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.halted⟩

def observedList (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,root =>
      match heap[root]? with
      | some .nil => some []
      | some (.pair head tail) =>
          match heap[head]?, observedList heap fuel tail with
          | some (.flag b),some bs => some (b::bs)
          | _,_ => none
      | _ => none

def retained (heap : NaturalHeap) (regs : Registers ℕ) (xs ys zs : Bits) : Bool :=
  observedList heap (xs.length+1) regs.a == some xs &&
  observedList heap (ys.length+1) regs.b == some ys &&
  observedList heap (zs.length+1) regs.c == some zs

def check (name : String) (t : Term) (xs ys zs suffix : Bits) : IO Unit := do
  let x := PackedWordPairTable.word xs PackedWordPairTable.empty
  let y := PackedWordPairTable.word ys x
  let z := PackedWordPairTable.word zs y
  let initial : BitState (capacity t) := ⟨z.heap,z.next,⟨x.root,y.root,z.root,[]⟩,[],entry t,suffix⟩
  let tr := execute (program t) (runSteps ![xs,ys,zs] t+2) initial
  let heap := (eraseState tr.state).heap
  let expected := evaluate ![xs,ys,zs] t
  unless tr.halted && tr.state.pc == exit t && tr.state.stack.isEmpty &&
      tr.state.source == suffix && tr.events.isEmpty &&
      observedList heap (expected.length+1) (value tr.state.registers.d) == some expected &&
      retained heap (eraseState tr.state).registers xs ys zs &&
      tr.state.heap.length == initial.heap.length+runCells ![xs,ys,zs] t &&
      value tr.state.next == tr.state.heap.length &&
      tr.operations ≤ completeBound (capacity t) (initial.heap.length+1) (initial.heap.length+1)
        (runSteps ![xs,ys,zs] t+1) do
    throw (IO.userError ("FAILED represented expression fixture: "++name))
  IO.println ("PASS represented expression "++name)
  (← IO.getStdout).flush

def checkSource (name : String) (t : Term) (xs ys zs suffix : Bits) : IO Unit := do
  IO.println ("START source expression "++name++" steps="++toString (InputExpressionProgram.instructions t xs ys zs))
  (← IO.getStdout).flush
  let initial := InputExpressionProgram.initial t
    (SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++SelfDelimitedWordProgram.encode zs++suffix)
  let tr := execute (InputExpressionProgram.program t) (InputExpressionProgram.instructions t xs ys zs+1) initial
  let heap := (eraseState tr.state).heap
  let expected := evaluate ![xs,ys,zs] t
  unless tr.halted && tr.state.pc == InputExpressionProgram.expressionLabel t (exit t) &&
      tr.state.stack.isEmpty && tr.state.source == suffix &&
      tr.events == (SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++SelfDelimitedWordProgram.encode zs).map Event.request &&
      observedList heap (expected.length+1) (value tr.state.registers.d) == some expected &&
      retained heap (eraseState tr.state).registers xs ys zs &&
      tr.state.heap.length == 3*(xs.length+ys.length+zs.length)+6+runCells ![xs,ys,zs] t &&
      value tr.state.next == tr.state.heap.length &&
      tr.operations ≤ completeBound (InputExpressionProgram.capacity t) 1 0
        (InputExpressionProgram.instructions t xs ys zs) do
    throw (IO.userError ("FAILED source expression fixture: "++name))
  IO.println ("PASS source expression "++name)
  (← IO.getStdout).flush

end DirectedFlowCutGap.ExpressionProgramSmoke

open DirectedFlowCutGap.ExpressionProgramSmoke DirectedFlowCutGap.ConcreteExpressionProgram in
def main : IO Unit := do
  let a : Term := .input 0
  let b : Term := .input 1
  let c : Term := .input 2
  let terms := [("input0",a),("input1",b),("input2",c),("empty",.nil),
    ("padded-literal",literal [true,false,false]),("add",.binary false a b),
    ("mul",.binary true a b),("all-inputs",.binary false (.binary true a b) c),
    ("saved-input2",.binary true (.binary false a c) (.binary false b c)),
    ("nested-right",.binary false a (.binary true b (.binary false a c))),
    ("literal-arithmetic",.binary true (literal [false,true]) (.binary false c (literal [true])))]
  for (name,t) in terms do
    check name t [true,true,false] [false,true] [true,false,false] [false,true]
  for (name,t) in terms do
    checkSource name t [true,true,false] [false,true] [true,false,false] [true,false]
  checkSource "all-empty" (.binary true (.binary false a b) c) [] [] [] [true]
  checkSource "all-padded-zero" (.binary false (.binary true a b) c) [false,false] [false] [false,false,false] []
  checkSource "carry-chain" (.binary true (.binary false a b) (.binary false c a))
    [true,true,true,true] [true] [true,true] [false]
  checkSource "packing-budget-zero" DirectedFlowCutGap.PackingBudgetProgram.body [] [] [] [true,false]
  checkSource "packing-budget-one" DirectedFlowCutGap.PackingBudgetProgram.body [true] [] [] [false,true]
  IO.println "PASS all 27 concrete expression fixtures"
