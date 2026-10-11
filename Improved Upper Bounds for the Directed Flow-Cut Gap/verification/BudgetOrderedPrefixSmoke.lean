import DirectedFlowCutGap.BudgetOrderedPrefixProgram

namespace DirectedFlowCutGap.BudgetOrderedPrefixSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal

structure Trace where
  state : BitState BudgetOrderedPrefixProgram.capacity
  events : List Event
  operations : ℕ
  halted : Bool

def execute : ℕ → BitState BudgetOrderedPrefixProgram.capacity → Trace
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt BudgetOrderedPrefixProgram.program s
      match a.result with
      | none => ⟨s,[],a.operations,true⟩
      | some r =>
          let t := execute fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.halted⟩

def observedList (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,root =>
      match heap[root]? with
      | some .nil => some []
      | some (.pair head tail) =>
          match heap[head]?,observedList heap fuel tail with
          | some (.flag b),some bs => some (b::bs)
          | _,_ => none
      | _ => none

def check (name : String) (n b s source : Bits) (expectedQuota : ℕ) : IO Unit := do
  let word := (BudgetOrderedPrefixProgram.word n b s).1
  let q := value word
  let encodedPrefix := SelfDelimitedWordProgram.encode n++SelfDelimitedWordProgram.encode b++SelfDelimitedWordProgram.encode s
  unless q==expectedQuota && q ≤ source.length do throw (IO.userError ("Bad fixture domain "++name))
  let initial := BudgetOrderedPrefixProgram.initial (encodedPrefix++source)
  let t := execute (BudgetOrderedPrefixProgram.steps n b s+1) initial
  let heap := (eraseState t.state).heap
  unless t.halted && t.state.pc==BudgetOrderedPrefixProgram.prefixLabel 29 &&
      t.state.stack.isEmpty && t.state.source==source.drop q &&
      t.events==(encodedPrefix++source.take q).map Event.request &&
      observedList heap (q+1) (value t.state.registers.b)==some (source.take q) &&
      t.state.heap.length==3*(n.length+b.length+s.length)+6+
        ConcreteExpressionProgram.runCells ![n,b,s] PackingBudgetProgram.body+4*q+3 &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ completeBound BudgetOrderedPrefixProgram.capacity 1 0 (BudgetOrderedPrefixProgram.steps n b s) do
    throw (IO.userError ("FAILED computed-budget ordered-prefix fixture "++name))
  IO.println ("PASS computed-budget ordered prefix "++name++" quota="++toString q)
  (← IO.getStdout).flush

end DirectedFlowCutGap.BudgetOrderedPrefixSmoke

open DirectedFlowCutGap.BudgetOrderedPrefixSmoke in
def main : IO Unit := do
  check "exact-six" [] [] [] [true,false,true,false,true,false] 6
  check "computed-ten-with-suffix" [] [true] []
    [true,false,false,true,true,false,true,false,true,true,false,true,false] 10
  IO.println "PASS both computed-budget ordered-prefix fixtures"
