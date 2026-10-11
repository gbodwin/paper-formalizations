import DirectedFlowCutGap.ValidatedFractionalRows
namespace DirectedFlowCutGap.SourceRowAcceptanceSmoke
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


def check (name : String) (rows : List (Bits × Bits)) (suffix : Bits) : IO Unit := do
  let source := SourceRowTableProgram.encode rows++suffix
  let t := execute SourceRowAcceptanceProgram.program (SourceRowAcceptanceProgram.instructions rows+1)
    (SourceRowAcceptanceProgram.initial source)
  let heap := (eraseState t.state).heap
  let recovered := table heap (SourceRowTableProgram.bits rows+2) (rows.length+1) (value t.state.registers.a)
  let rejected := rows.any (fun p => value p.2==0)
  let visited := (rows.takeWhile (fun p => 0 < value p.2)).length+1
  unless t.halted && t.state.pc==(if rejected then 59 else 58) && t.state.stack.isEmpty &&
      t.state.source==suffix && recovered==some rows &&
      heap[value t.state.registers.d]?==some (.flag rejected) &&
      t.events==((SourceRowTableProgram.encode rows).map Event.request) &&
      t.state.heap.length==SourceRowTableProgram.cells rows+visited &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ 40000000*(SourceRowTableProgram.bits rows+rows.length+1)^3 do
    throw (IO.userError ("FAILED actual whole-row acceptance: "++name))
  IO.println ("PASS actual whole-row acceptance "++name)
end DirectedFlowCutGap.SourceRowAcceptanceSmoke
open DirectedFlowCutGap.SourceRowAcceptanceSmoke in
 def main : IO Unit := do
  check "empty table" [] [true,false]
  check "positive singleton" [([false,true],[true])] [false,true]
  check "empty denominator" [([],[])] [true,true]
  check "padded zero" [([true],[false,false,false])] [false,false]
  check "first zero keeps tail" [([],[false]),([true],[true]),([false,true],[true,false])] [true,false,true]
  check "middle zero keeps all rows" [([true],[true]),([],[]),([false],[true,true])] []
  check "last zero" [([],[true,false]),([true],[false,true]),([true,true],[false,false])] [true]
  check "all padded positives" [([false,false],[false,true,false]),([],[true,false,false]),([true],[false,false,true])] [false]
  check "long late positive" [([],List.replicate 7 false++[true,false])] [false,true,false]
  check "long zero after positive" [([],[true]),([true],List.replicate 8 false)] [true,true,false]
  IO.println "PASS all10 actual whole-row acceptance fixtures"
