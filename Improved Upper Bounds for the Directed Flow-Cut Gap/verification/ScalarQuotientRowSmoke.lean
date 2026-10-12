import DirectedFlowCutGap.ScalarQuotientRowRefinement
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.ScalarQuotientRowSmoke
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

def prepareScalar (x : Fraction) (s : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let num := PackedWordPairTable.word x.num s
  let den := PackedWordPairTable.word x.den num
  PackedWordPairTable.allocate (.pair num.root den.root) den

def check (name : String) (mode : Bool) (scalar : Fraction) (xs : List Fraction) : IO Unit := do
  let row := prepare xs ⟨[],[],[],0⟩
  let sc := prepareScalar scalar row
  let initial : BitState 182 := ⟨sc.heap,sc.next,⟨row.root,sc.root,[],[]⟩,[],180,[true,false,true]⟩
  let count := 1+ScalarQuotientRow.steps mode scalar xs
  let cells := ScalarQuotientRow.cells mode scalar xs
  let actual := execute (ScalarQuotientRow.program mode) (count+1) initial
  let heap := (eraseState actual.state).heap
  let expected := ScalarQuotientRow.result mode scalar xs
  let bound := ScalarQuotientRow.instructionBound xs.length (width (scalar::xs))
  unless actual.halted && actual.instructions==count && count≤bound &&
      readRow heap (heap.length+1) (value actual.state.registers.d)==some (fields expected) &&
      readRow heap (heap.length+1) (value row.root)==some (fields xs) &&
      readFraction heap (value sc.root)==some (scalar.num,scalar.den) &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 182 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED scalar row "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual scalar row "++name++" steps="++toString count)

def main : IO Unit := do
  check "empty-denominator" false padded []
  check "empty-numerator" true padded []
  check "zero-scalar" false (frac 0 0) [padded,frac 3 1]
  check "padded-zero-scalar" false ⟨[false,false],[true],by decide⟩ [padded]
  check "zero-row-entry" true padded [frac 0 0,frac 2 1]
  check "ordered-denominator" false (frac 3 1) [frac 2 0,frac 1 2]
  check "ordered-numerator" true (frac 3 1) [frac 2 0,frac 1 2]
  check "padded-both" true padded [padded,padded]
end DirectedFlowCutGap.ScalarQuotientRowSmoke

def main : IO Unit := DirectedFlowCutGap.ScalarQuotientRowSmoke.main
