import DirectedFlowCutGap.ActualPackingParameters
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PackingParametersSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead BinaryRational
structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  instructions : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) (fuel : ℕ) (s : BitState C) : Trace C :=
  go fuel s [] 0 0
where
  go : ℕ → BitState C → List Event → ℕ → ℕ → Trace C
  | 0,s,events,operations,instructions => ⟨s,events.reverse,operations,instructions,false⟩
  | fuel+1,s,events,operations,instructions =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,events.reverse,operations+a.operations,instructions,true⟩
      | some r => go fuel r.state (r.events.reverse++events) (operations+a.operations) (instructions+1)

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


def readParameters (heap : NaturalHeap) (root : ℕ) : Option ((Bits×Bits)×Bits) := do
  let some (.pair delta fuel) := heap[root]? | none
  return (←readFraction heap delta,←readBits heap (heap.length+1) fuel)

def check (name : String) (row : List Fraction) : IO Unit := do
  let prepared := prepare row ⟨[],[],[],0⟩
  let initial : BitState 360 := ⟨prepared.heap,prepared.next,⟨prepared.root,[],[],[]⟩,[],310,[true,false,true]⟩
  let count := PackingParameters.steps row.length
  let actual := execute PackingParameters.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let old := BinaryFractionalCore.parameters (BinaryCounters.lengthBits (row.map fun _ => false)).1
  unless actual.halted && actual.instructions==count && count≤PackingParameters.instructionBound row.length &&
      readParameters heap (value actual.state.registers.d)==some ((old.delta.num,old.delta.den),old.fuel) &&
      readRow heap (heap.length+1) (value prepared.root)==some (fields row) &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.pc==328 && actual.state.heap.take initial.heap.length==initial.heap &&
      value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 360 (initial.heap.length+1) (initial.heap.length+1) (PackingParameters.instructionBound row.length) do
    throw (IO.userError ("FAILED actual parameter construction "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual parameter construction "++name++" steps="++toString count)

def main : IO Unit := do
  check "empty-zero-fuel" []
  check "one-positive" [frac 3 1]
  check "one-zero" [frac 0 0]
  check "one-padded" [padded]
  check "two-mixed" [padded,frac 2 2]
  check "three-zero" [frac 0 0,frac 0 0,frac 0 0]
  check "four" (List.replicate 4 (frac 1 0))
  check "five-padded" (List.replicate 5 padded)
end DirectedFlowCutGap.PackingParametersSmoke

def main : IO Unit := DirectedFlowCutGap.PackingParametersSmoke.main
