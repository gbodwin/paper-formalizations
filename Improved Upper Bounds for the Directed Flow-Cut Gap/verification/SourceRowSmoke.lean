import DirectedFlowCutGap.SourceRowReadProgram

namespace DirectedFlowCutGap.SourceRowSmoke
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

def checkBuild (name : String) (rows : List (Bits × Bits)) (suffix : Bits) : IO Unit := do
  let source := SourceRowTableProgram.encode rows++suffix
  let t := execute SourceRowTableProgram.program (SourceRowTableProgram.steps rows+2)
    (SourceRowTableProgram.initial source)
  let heap := (eraseState t.state).heap
  unless t.halted && t.state.pc==31 && t.state.stack.isEmpty && t.state.source==suffix &&
      table heap (SourceRowTableProgram.bits rows+2) (rows.length+2) (value t.state.registers.d)==some rows &&
      t.events==(SourceRowTableProgram.encode rows).map Event.request &&
      t.state.heap.length==SourceRowTableProgram.cells rows && value t.state.next==t.state.heap.length &&
      t.operations ≤ 10000000*(SourceRowTableProgram.bits rows+rows.length+1)^3 do
    throw (IO.userError ("FAILED source row build: "++name))
  IO.println ("PASS source row build "++name)

def checkRead (name : String) (rows : List (Bits × Bits)) (index suffix : Bits) : IO Unit := do
  let source := SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode index++suffix
  let t := execute SourceRowReadProgram.program (SourceRowReadProgram.instructions rows index+1)
    (SourceRowReadProgram.initial source)
  let heap := (eraseState t.state).heap
  let expected := rows[value index]?
  let num := word heap (SourceRowTableProgram.bits rows+2) (value t.state.registers.a)
  let den := word heap (SourceRowTableProgram.bits rows+2) (value t.state.registers.b)
  unless (value index < rows.length) && t.halted && t.state.pc==66 && t.state.stack.isEmpty &&
      t.state.source==suffix && num==expected.map Prod.fst && den==expected.map Prod.snd &&
      t.events==((SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode index).map Event.request) &&
      t.state.heap.length==SourceRowTableProgram.cells rows+3*index.length+value index+3 &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ 100000000*(SourceRowTableProgram.bits rows+rows.length+index.length+1)^3 do
    throw (IO.userError ("FAILED source row read: "++name))
  IO.println ("PASS source row read "++name)

end DirectedFlowCutGap.SourceRowSmoke

open DirectedFlowCutGap.SourceRowSmoke in
def main : IO Unit := do
  let rows := [([false,true,false,false],[true,false,false]),([],[]),([true,true],[false,true])]
  checkBuild "empty" [] [true,false]
  checkBuild "empty-fields" [([],[])] [false,true]
  checkBuild "padded-fields" rows [true,true,false]
  checkBuild "all-zero-padding" [([false,false],[false,false,false])] []
  checkBuild "six-rows" (rows++rows) [true]
  checkRead "empty-fields-zero" [([],[])] [] [true,false]
  checkRead "empty-fields-padded-zero" [([],[])] [false,false,false] [false,true]
  checkRead "first" rows [] [true,false]
  checkRead "middle" rows [true] [false,true]
  checkRead "last" rows [false,true] [true,true]
  checkRead "last-padded" rows [false,true,false,false] []
  checkRead "six-first" (rows++rows) [false] [true]
  checkRead "six-fourth" (rows++rows) [true,true] [false]
  checkRead "six-fifth" (rows++rows) [false,false,true] [true,false]
  checkRead "six-last-padded" (rows++rows) [true,false,true,false] [false,true]
  IO.println "PASS all15 source row constructor/read fixtures"
