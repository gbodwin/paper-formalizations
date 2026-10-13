import DirectedFlowCutGap.ActualPackingAmount
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PackingAmountSmoke
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



def scalar (x : Fraction) (s : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let num := PackedWordPairTable.word x.num s
  let den := PackedWordPairTable.word x.den num
  PackedWordPairTable.allocate (.pair num.root den.root) den

def prepareFlags : List Bool → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | b::bs,s =>
    let tail := prepareFlags bs s
    let head := PackedWordPairTable.allocate (.flag b) tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

def check (name : String) (rows : List Fraction) (word : Bits) : IO Unit := do
  let table := prepare rows ⟨[],[],[],0⟩
  let mask := prepareFlags (rows.map fun _ => true) table
  let index := PackedWordPairTable.word word mask
  let choice := PackedWordPairTable.allocate (.pair mask.root index.root) index
  let initial : BitState 44 := ⟨choice.heap,choice.next,⟨choice.root,table.root,[],[]⟩,[],40,[true,false]⟩
  let count := BinaryIndexedPairRead.steps word+6
  let expected := IndexedRationalRead.lookup rows word
  let actual := execute PackingAmount.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let decoded := readFraction heap (value actual.state.registers.d)
  let bound := PackingAmount.instructionBound rows.length word.length
  unless actual.halted && actual.instructions==count && decoded==some (expected.num,expected.den) &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+value word+2 &&
      value actual.state.next==actual.state.heap.length && actual.events.isEmpty &&
      actual.state.source==initial.source && actual.state.stack.isEmpty && actual.state.pc==42 &&
      count≤bound && actual.operations≤completeBound 44 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED actual amount "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual amount "++name++" steps="++toString count)

def main : IO Unit := do
  check "zero" [zero] []
  check "one" [one] [false,false]
  check "second" [one,padded] [true]
  check "padded-index" [one,padded] [true,false,false]
  check "last" [zero,one,frac 2 4] [false,true]
  check "duplicate" [one,one,one] [false,true,false]
  check "padded-fields" [padded] []
  check "fourth" [zero,padded,one,frac 3 2] [true,true]
end DirectedFlowCutGap.PackingAmountSmoke

def main := DirectedFlowCutGap.PackingAmountSmoke.main
