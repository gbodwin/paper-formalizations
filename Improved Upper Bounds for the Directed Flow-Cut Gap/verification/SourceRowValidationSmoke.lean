import DirectedFlowCutGap.SourceRowValidationProgram
namespace DirectedFlowCutGap.SourceRowValidationSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
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

def word (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,root =>
      match heap[root]? with
      | some .nil => some []
      | some (.pair head tail) =>
          match heap[head]?,word heap fuel tail with
          | some (.flag b),some bs => some (b::bs)
          | _,_ => none
      | _ => none

def table (heap : NaturalHeap) (wordFuel : ℕ) : ℕ → ℕ → Option (List (Bits × Bits))
  | 0,_ => none
  | fuel+1,root =>
      match heap[root]? with
      | some .nil => some []
      | some (.pair item tail) =>
          match heap[item]?,table heap wordFuel fuel tail with
          | some (.pair a b),some rows =>
              match word heap wordFuel a,word heap wordFuel b with
              | some x,some y => some ((x,y)::rows)
              | _,_ => none
          | _,_ => none
      | _ => none


def check (name : String) (rows : List (Bits × Bits)) (index suffix : Bits) : IO Unit := do
  let source := SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode index++suffix
  let expected := rows[value index]?
  let denBits := (expected.map Prod.snd).getD []
  let count := SourceRowReadProgram.instructions rows index+BinaryZeroProgram.steps denBits+4
  let t := execute SourceRowValidationProgram.program (count+1) (SourceRowValidationProgram.initial source)
  let heap := (eraseState t.state).heap
  let num := word heap (SourceRowTableProgram.bits rows+2) (value t.state.registers.a)
  let den := word heap (SourceRowTableProgram.bits rows+2) (value t.state.registers.b)
  let rejected := (isZero denBits).1
  unless (value index < rows.length) && t.halted && t.state.pc==78 && t.state.stack.isEmpty &&
      t.state.source==suffix && num==expected.map Prod.fst && den==expected.map Prod.snd &&
      heap[value t.state.registers.d]?==some (.flag rejected) && rejected==(value denBits==0) &&
      t.events==((SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode index).map Event.request) &&
      t.state.heap.length==SourceRowTableProgram.cells rows+3*index.length+value index+4 &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ 200000000*(SourceRowTableProgram.bits rows+rows.length+index.length+1)^3 do
    throw (IO.userError ("FAILED actual denominator validation: "++name))
  IO.println ("PASS actual denominator validation "++name)
end DirectedFlowCutGap.SourceRowValidationSmoke
open DirectedFlowCutGap.SourceRowValidationSmoke in
 def main : IO Unit := do
  let rows := [([false,true,false],[false,false,false]),([],[]),([true,true],[false,true,false]),([false],[true,false,false])]
  check "empty denominator" [([],[])] [] [true,false]
  check "padded zero" rows [] [false,true]
  check "second empty" rows [true,false,false] [true,true]
  check "late nonzero" rows [false,true] [false,false]
  check "early nonzero" rows [true,true] [true,false,true]
  check "single one" [([],[true])] [] []
  check "long padded zero" [([true],List.replicate 8 false)] [false,false] [true]
  check "long late one" [([],List.replicate 7 false++[true,false])] [] [false]
  IO.println "PASS all8 actual source denominator-validation fixtures"
