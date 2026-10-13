import DirectedFlowCutGap.ActualGridFuel
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.GridFuelSmoke
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


def check (name : String) (xs ys expected : Bits) : IO Unit := do
  let l := PackedWordPairTable.word xs PackedWordPairTable.seed
  let r := PackedWordPairTable.word ys l
  let source := [false,true,false]
  let initial : BitState 256 := ⟨r.heap,r.next,⟨l.root,r.root,l.root,[]⟩,[],254,source⟩
  let old := (eraseState initial).heap
  let count := GridFuelProgram.steps xs ys+1
  let actual := execute GridFuelProgram.program (count+1) initial
  let final := eraseState actual.state
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==255 && final.stack==[] && final.source==source &&
      readBits final.heap (final.heap.length+1) final.registers.d==some expected &&
      readBits final.heap (final.heap.length+1) (value l.root)==some xs &&
      readBits final.heap (final.heap.length+1) (value r.root)==some ys &&
      final.heap.take old.length==old && final.heap.length==old.length+GridFuelProgram.cells xs ys &&
      actual.operations≤completeBound 256 (old.length+1) (old.length+1) (GridFuelProgram.inputSteps xs ys) do
    throw (IO.userError ("FAIL actual grid fuel "++name))
  IO.println ("PASS actual grid fuel "++name++" steps="++toString actual.instructions)

def main (args : List String) : IO Unit := do
  if args.head?==some "larger" then
    check "two-width-two" [false,true] [false,true] [true,true,false,true]
    check "four-width-three" [false,false,true] [true,true] [true,true,true,true]
    check "padded-four-three" [false,false,true,false,false] [true,true,false] [true,true,true,true]
    check "seventeen-five" [true,false,false,false,true] [true,false,true] [true,true,true,false,true]
    check "width-sixteen" [true] [false,false,false,false,true] [true,false,true,false,false,true]
    check "zero-width-eight" [] [false,false,false,true] [true,true,false,false,true]
  else
    check "empty" [] [] [true,true]
    check "padded-zero" [false,false] [false,false,false] [true,true]
    check "one-zero" [true] [] [true,false,true]
    check "two-zero" [false,true] [] [true,true,true]
    check "padded-one" [true,false,false] [false] [true,false,true]
    check "zero-width-one" [] [true,false] [true,false,true]
end DirectedFlowCutGap.GridFuelSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.GridFuelSmoke.main args
