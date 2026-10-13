import DirectedFlowCutGap.ActualFractionWidth
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.FractionWidthSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
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


def check (name : String) (num den expected : Bits) : IO Unit := do
  if h : 0<value den then
    let q : BinaryRational.Fraction := ⟨num,den,h⟩
    let l := PackedWordPairTable.word num PackedWordPairTable.seed
    let r := PackedWordPairTable.word den l
    let recd := PackedWordPairTable.allocate (.pair l.root r.root) r
    let source := [true,false,false,true]
    let initial : BitState 128 := ⟨recd.heap,recd.next,⟨recd.root,l.root,r.root,[]⟩,[],126,source⟩
    let old := (eraseState initial).heap
    let count := FractionWidthProgram.steps q+1
    let actual := execute FractionWidthProgram.program (count+1) initial
    let final := eraseState actual.state
    unless actual.halted && actual.instructions==count && actual.events==[] &&
        final.pc==127 && final.stack==[] && final.source==source &&
        final.registers.a==value recd.root && final.registers.b==value l.root && final.registers.c==value r.root &&
        readBits final.heap (final.heap.length+1) final.registers.d==some expected &&
        readBits final.heap (final.heap.length+1) (value l.root)==some num &&
        readBits final.heap (final.heap.length+1) (value r.root)==some den &&
        final.heap.take old.length==old && final.heap.length==old.length+FractionWidthProgram.cells q &&
        actual.operations≤completeBound 128 (old.length+1) (old.length+1) (FractionWidthProgram.inputSteps q) do
      throw (IO.userError ("FAIL actual fraction width "++name))
    IO.println ("PASS actual fraction width "++name++" steps="++toString actual.instructions)
  else throw (IO.userError "invalid fixture denominator")

def main : IO Unit := do
  check "zero-one" [] [true] [true]
  check "padded-zero-one" [false,false,false] [true,false,false] [true]
  check "one-one" [true] [true] [true]
  check "two-one" [false,true] [true] [false,true]
  check "one-two" [true] [false,true] [false,true]
  check "equal-two-bit" [true,true] [false,true] [false,true]
  check "four-two" [false,false,true] [false,true] [true,true]
  check "one-eight" [true] [false,false,false,true] [false,false,true]
  check "seven-bit-numerator" [true,true,true,true,true,true,true] [true] [true,true,true]
  check "nine-bit-numerator" [false,false,false,false,false,false,false,false,true] [false,true] [true,false,false,true]
  check "padded-equal-width" [true,true,false,false] [false,true,false,false,false] [false,true]
  check "padded-denominator" [true,false,false] [true,false,true,false,false,false] [true,true]
end DirectedFlowCutGap.FractionWidthSmoke

def main : IO Unit := DirectedFlowCutGap.FractionWidthSmoke.main
