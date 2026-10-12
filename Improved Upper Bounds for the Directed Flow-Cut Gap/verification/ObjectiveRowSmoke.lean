import DirectedFlowCutGap.ActualObjectiveRow
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.ObjectiveRowSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead BinaryRational
structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  instructions : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) : ℕ → BitState C → Trace C
  | 0,s => ⟨s,[],0,0,false⟩
  | fuel+1,s =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,[],a.operations,0,true⟩
      | some r =>
          let t := execute p fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.instructions+1,t.halted⟩

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

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def padded : Fraction := ⟨[true,false,false],[false,true,false],by decide⟩


def prepare : List Fraction → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | x::xs,s =>
    let tail := prepare xs s
    let num := PackedWordPairTable.word x.num tail
    let den := PackedWordPairTable.word x.den num
    let q := PackedWordPairTable.allocate (.pair num.root den.root) den
    PackedWordPairTable.allocate (.pair q.root tail.root) q

def readRow (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits×Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair q rest) => do
      let value ← readFraction heap q
      return value::(←readRow heap fuel rest)
    | _ => none

def fields (xs : List Fraction) := xs.map fun x => (x.num,x.den)
def width (xs : List Fraction) := (xs.map fun x => max x.num.length x.den.length).foldl max 0

def check (name : String) (xs ys : List Fraction) : IO Unit := do
  let left := prepare xs ⟨[],[],[],0⟩
  let right := prepare ys left
  let initial : BitState 312 := ⟨right.heap,right.next,⟨left.root,right.root,[],[]⟩,[],308,[true,false,true]⟩
  let count := ObjectiveRow.steps xs ys
  let cells := ObjectiveRow.cells xs ys
  let actual := execute ObjectiveRow.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let expected := ObjectiveRow.result xs ys
  let bound := ObjectiveRow.instructionBound xs.length (max (width xs) (width ys))
  unless xs.length==ys.length && actual.halted && actual.instructions==count && count≤bound &&
      readFraction heap (value actual.state.registers.d)==some (expected.num,expected.den) &&
      readRow heap (heap.length+1) (value actual.state.registers.a)==some (fields (ObjectiveProductList.products xs ys)) &&
      readRow heap (heap.length+1) (value left.root)==some (fields xs) &&
      readRow heap (heap.length+1) (value right.root)==some (fields ys) &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 312 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED actual objective "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual objective "++name++" steps="++toString count)

def main : IO Unit := do
  check "empty" [] []
  check "zero" [frac 0 0] [frac 3 1]
  check "integer" [frac 2 0] [frac 3 0]
  check "padded" [padded] [padded]
  check "ordered-two" [frac 1 0,frac 2 0] [frac 3 0,frac 1 0]
  check "mixed-denominators" [frac 1 1,frac 2 2] [frac 3 3,frac 1 1]
  check "zero-among-three" [frac 0 1,frac 1 0,frac 2 1] [frac 2 0,frac 2 1,frac 0 0]
  check "repeated-values" [padded,padded] [frac 2 0,frac 2 0]
end DirectedFlowCutGap.ObjectiveRowSmoke

def main : IO Unit := DirectedFlowCutGap.ObjectiveRowSmoke.main
