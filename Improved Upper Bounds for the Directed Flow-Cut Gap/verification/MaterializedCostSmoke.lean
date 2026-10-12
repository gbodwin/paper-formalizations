import DirectedFlowCutGap.MaterializedGraphPath
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.MaterializedCostSmoke
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
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

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none

def readFraction (heap : NaturalHeap) (p : ℕ) : Option (Bits×Bits) := do
  let some (.pair num den) := heap[p]? | none
  return (←readBits heap (heap.length+1) num,←readBits heap (heap.length+1) den)

def checkCommon {C : ℕ} (name : String) (initial : BitState C) (t : Trace C) (steps cells : ℕ) : IO Unit := do
  unless t.halted && t.events.isEmpty && t.state.source==initial.source &&
      t.state.stack.isEmpty && t.state.heap.take initial.heap.length==initial.heap &&
      t.state.heap.length==initial.heap.length+cells &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ completeBound C (initial.heap.length+1) (initial.heap.length+1) steps do
    throw (IO.userError ("FAILED materialized-cost machine invariants: "++name))

def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | w::ws,s =>
    let t := wordList ws s
    let h := PackedWordPairTable.word w t
    PackedWordPairTable.allocate (.pair h.root t.root) h

def readFractions (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits×Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      let x ← readFraction heap head
      let xs ← readFractions heap fuel tail
      return x::xs
    | _ => none

def build (rows : List Fraction) (sw : Bits) : PackedWordPairTable.Prepared :=
  let table := PackedWordPairTable.construct (rows.map fun x => (x.num,x.den))
  let source := PackedWordPairTable.word sw table
  PackedWordPairTable.allocate (.pair table.root source.root) source

def checkRead (name : String) (rows : List Fraction) (sw word : Bits) : IO Unit := do
  let context := build rows sw
  let input := PackedWordPairTable.word word context
  let initial : BitState 111 := ⟨input.heap,input.next,⟨input.root,context.root,[],[]⟩,[],109,[true,false,true]⟩
  let steps := OutgoingCostProgram.instructions sw word+1
  let t := execute OutgoingCostProgram.program (steps+1) initial
  let expected := OutgoingCostProgram.result rows sw word
  checkCommon name initial t steps (OutgoingCostProgram.cells sw word)
  unless t.state.pc==110 && readFraction (eraseState t.state).heap (value t.state.registers.d)==some (expected.num,expected.den) do
    throw (IO.userError ("FAILED actual outgoing read: "++name))
  IO.println ("PASS actual outgoing access "++name)

def checkMaterialize (name : String) (rows : List Fraction) (sw : Bits) (words : List Bits) : IO Unit := do
  let context := build rows sw
  let input := wordList words context
  let initial : BitState 124 := ⟨input.heap,input.next,⟨input.root,context.root,[],[]⟩,[],122,[false,true,false]⟩
  let steps := PathCostMaterialization.steps sw words+1
  let t := execute PathCostMaterialization.program (steps+1) initial
  let expected := (PathCostMaterialization.costs rows sw words).map fun x => (x.num,x.den)
  checkCommon name initial t steps (PathCostMaterialization.cells sw words)
  unless t.state.pc==123 && readFractions (eraseState t.state).heap (t.state.heap.length+1)
      (value t.state.registers.d)==some expected do
    throw (IO.userError ("FAILED actual cost-list materialization: "++name))
  IO.println ("PASS actual cost-list materialization "++name)

def checkSum (name : String) (rows : List Fraction) (sw : Bits) (words : List Bits) : IO Unit := do
  let context := build rows sw
  let input := wordList words context
  let initial : BitState 284 := ⟨input.heap,input.next,⟨input.root,context.root,[],[]⟩,[],282,[true,true,false]⟩
  let steps := MaterializedPathSum.steps rows sw words+1
  let t := execute MaterializedPathSum.program (steps+1) initial
  let expected := MaterializedPathSum.result rows sw words
  checkCommon name initial t steps (MaterializedPathSum.cells rows sw words)
  unless t.state.pc==283 && readFraction (eraseState t.state).heap (value t.state.registers.d)==some (expected.num,expected.den) do
    throw (IO.userError ("FAILED actual materialized sum: "++name))
  IO.println ("PASS actual materialized sum "++name)

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def padded : Fraction := ⟨[true,false,false],[false,true,false],by decide⟩
def rows : List Fraction := [frac 5 2,padded,frac 2 4]
def main : IO Unit := do
  checkRead "source zero" rows [] [false,false]
  checkRead "above source" rows [] [true,false]
  checkRead "below source" rows [false,true] []
  checkRead "padded equal" rows [false,true,false] [false,true]
  checkRead "last record" rows [] [false,true,false]
  checkMaterialize "empty graph and path" [] [] []
  checkMaterialize "source only" rows [false,false] [[]]
  checkMaterialize "mixed order" rows [] [[false,true],[true],[false]]
  checkMaterialize "repeated records" rows [false,true] [[true,false],[true],[]]
  checkMaterialize "padding retained" rows [] [[true,false,false]]
  checkSum "empty graph and path" [] [] []
  checkSum "source only" rows [] [[false,false]]
  checkSum "different denominators" rows [] [[true],[false,true]]
  checkSum "repeat source convention" rows [true] [[true],[],[true]]
  checkSum "three repeated reads" rows [] [[true],[true,false],[true,false,false]]
  checkSum "mixed padded path" rows [false,true,false] [[],[true,false],[false,true]]
  IO.println "MATERIALIZED_COST_ACTUAL_FIXTURES passed: 16 cases"
end DirectedFlowCutGap.MaterializedCostSmoke

def main : IO Unit := DirectedFlowCutGap.MaterializedCostSmoke.main
