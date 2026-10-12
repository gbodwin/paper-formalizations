import DirectedFlowCutGap.ActualRationalQuotient
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.QuotientSmoke
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



def prepare (x : Fraction) (s : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let num := PackedWordPairTable.word x.num s
  let den := PackedWordPairTable.word x.den num
  PackedWordPairTable.allocate (.pair num.root den.root) den

def check (name : String) (x y : Fraction) : IO Unit := do
  let left := prepare x ⟨[],[],[],0⟩
  let right := prepare y left
  let initial : BitState 164 := ⟨right.heap,right.next,⟨left.root,right.root,[],[]⟩,[],161,[true,false,true]⟩
  let count := 1+CanonicalRationalQuotient.steps x y
  let cells := CanonicalRationalQuotient.cells x y
  let actual := execute CanonicalRationalQuotient.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let expected := (BinaryRational.div x y).1
  let bound := 600*(CanonicalRationalQuotient.inputSize x y)^2
  unless actual.halted && actual.instructions==count && count≤bound &&
      readFraction heap (value actual.state.registers.d)==some (expected.num,expected.den) &&
      readFraction heap (value left.root)==some (x.num,x.den) &&
      readFraction heap (value right.root)==some (y.num,y.den) &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 164 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED actual quotient "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual quotient "++name++" steps="++toString count)

def main : IO Unit := do
  check "zero-divisor" (frac 3 1) (frac 0 0)
  check "padded-zero-divisor" (frac 3 1) ⟨[false,false,false],[true,false],by decide⟩
  check "zero-numerator" (frac 0 0) (frac 3 1)
  check "both-zero" (frac 0 1) (frac 0 2)
  check "integers" (frac 6 0) (frac 2 0)
  check "proper-fractions" (frac 2 2) (frac 3 3)
  check "unreduced-fields" (frac 2 3) (frac 1 1)
  check "padded-both" padded padded
end DirectedFlowCutGap.QuotientSmoke

def main : IO Unit := DirectedFlowCutGap.QuotientSmoke.main
