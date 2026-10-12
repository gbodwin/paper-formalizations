import DirectedFlowCutGap.ActualPackingEntry
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PackingEntrySmoke
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

def check (name : String) (ci amount y : Fraction) : IO Unit := do
  let cap := scalar ci ⟨[],[],[],0⟩
  let amt := scalar amount cap
  let old := scalar y amt
  let initial : BitState 480 := ⟨old.heap,old.next,⟨cap.root,amt.root,old.root,[]⟩,[],440,[false,true]⟩
  let count := PackingEntry.steps ci amount y
  let expected := PackingEntry.result ci amount y
  let actual := execute PackingEntry.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let decoded := readFraction heap (value actual.state.registers.d)
  let B := width [ci,amount,y]
  let bound := PackingEntry.instructionBound B
  unless actual.halted && actual.instructions==count && decoded==some (expected.num,expected.den) &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+PackingEntry.cells ci amount y &&
      value actual.state.next==actual.state.heap.length && actual.events.isEmpty &&
      actual.state.source==initial.source && actual.state.stack.isEmpty && actual.state.pc==467 &&
      count≤bound && actual.operations≤completeBound 480 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED actual entry "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual entry "++name++" steps="++toString count)

def main : IO Unit := do
  check "one" one one one
  check "zero-capacity" zero one one
  check "zero-amount" one zero one
  check "zero-weight" one one zero
  check "fractional" (frac 1 1) (frac 2 2) (frac 1 2)
  check "padded" padded padded padded
end DirectedFlowCutGap.PackingEntrySmoke

def main := DirectedFlowCutGap.PackingEntrySmoke.main
