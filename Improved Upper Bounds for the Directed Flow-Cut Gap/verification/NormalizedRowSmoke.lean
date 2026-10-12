import DirectedFlowCutGap.ActualNormalizedRow
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.NormalizedRowSmoke
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

def check (name : String) (xs : List Fraction) (mask : List Bool) : IO Unit := do
  let row := prepare xs ⟨[],[],[],0⟩
  let flags := PackedWordPairTable.word mask row
  let initial : BitState 372 := ⟨flags.heap,flags.next,⟨row.root,flags.root,[],[]⟩,[],364,[true,false,true]⟩
  let count := NormalizedRow.steps xs mask
  let cells := NormalizedRow.cells xs mask
  let actual := execute NormalizedRow.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let expected := NormalizedRow.result xs mask
  let scalar := NormalizedRow.alpha xs mask
  let maskedRoot := value initial.next+MaskedRationalRow.cells mask
  let bound := NormalizedRow.instructionBound xs.length (width xs)
  unless xs.length==mask.length && actual.halted && actual.instructions==count && count≤bound &&
      readRow heap (heap.length+1) (value actual.state.registers.d)==some (fields expected) &&
      readFraction heap (value actual.state.registers.b)==some (scalar.num,scalar.den) &&
      readRow heap (heap.length+1) maskedRoot==some (fields (MaskedRationalRow.result xs mask)) &&
      readRow heap (heap.length+1) (value row.root)==some (fields xs) &&
      readBits heap (heap.length+1) (value flags.root)==some mask &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 372 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED normalized row "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual normalized row "++name++" steps="++toString count)

def main : IO Unit := do
  check "empty" [] []
  check "false-positive" [frac 3 1] [false]
  check "true-zero" [frac 0 0] [true]
  check "true-padded" [padded] [true]
  check "mixed-order" [frac 1 1,frac 2 2] [false,true]
  check "reverse-mixed" [frac 1 1,frac 2 2] [true,false]
  check "all-false" [padded,frac 2 0] [false,false]
  check "all-true" [frac 1 0,frac 2 1] [true,true]
end DirectedFlowCutGap.NormalizedRowSmoke

def main : IO Unit := DirectedFlowCutGap.NormalizedRowSmoke.main
