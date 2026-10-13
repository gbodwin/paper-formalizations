import DirectedFlowCutGap.OriginalInputWidth
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.InputWidthSmoke
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


def costs : List (Bits × Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | r::rs,s => PackedWordPairTable.prepend r (costs rs s)

def fractions : List (Bits × Bits) → Option (List BinaryRational.Fraction)
  | [] => some []
  | (num,den)::cs => if h : 0<value den then
      (fractions cs).map (⟨num,den,h⟩::·) else none

def readTable (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits × Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair h t) => do
      let .pair num den ← heap[h]? | none
      let ns ← readBits heap (heap.length+1) num
      let ds ← readBits heap (heap.length+1) den
      let rest ← readTable heap fuel t
      pure ((ns,ds)::rest)
    | _ => none

def check (name : String) (cs : List (Bits × Bits)) (expected : Bits) : IO Unit := do
  IO.println ("BEGIN actual input width "++name)
  (←IO.getStdout).flush
  let some rows := fractions cs | throw (IO.userError "invalid fixture denominator")
  let prepared := costs cs PackedWordPairTable.seed
  let source := [true,false,true]
  let initial : BitState 208 := ⟨prepared.heap,prepared.next,⟨prepared.root,prepared.root,prepared.root,[]⟩,[],206,source⟩
  let old := (eraseState initial).heap
  let count := InputWidthProgram.steps rows+1
  let actual := execute InputWidthProgram.program (count+1) initial
  let final := eraseState actual.state
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==207 && final.stack==[] && final.source==source &&
      final.registers.a==value prepared.root && final.registers.b==value prepared.root && final.registers.c==value prepared.root &&
      readBits final.heap (final.heap.length+1) final.registers.d==some expected &&
      readTable final.heap (final.heap.length+1) (value prepared.root)==some cs &&
      final.heap.take old.length==old && final.heap.length==old.length+InputWidthProgram.cells rows &&
      actual.operations≤completeBound 208 (old.length+1) (old.length+1) (InputWidthProgram.inputSteps rows) do
    throw (IO.userError ("FAIL actual input width "++name))
  IO.println ("PASS actual input width "++name++" steps="++toString actual.instructions)

def main (args : List String) : IO Unit := do
  if args==["rows"] then
    check "larger-head" [([false,false,false,true],[true]),([true],[false,true])] [false,false,true]
    check "larger-tail" [([true],[true]),([true,true,true,true,true,true,true],[true])] [true,true,true]
    check "increasing" [([true],[true]),([false,true],[true]),([false,false,true],[true])] [true,true]
    check "zero-numerators" [([],[true]),([false,false],[false,true]),([],[true,false,true])] [true,true]
    check "padded-duplicate-widths" [([true,true,false],[true]),([false,true,false,false],[true,false]),([true],[false,true,false])] [false,true]
    check "mixed-three" [([false,true],[true,true]),([],[true]),([true,false],[false,false,false,true])] [false,false,true]
  else
    check "empty" [] []
    check "zero-one" [([],[true])] [true]
    check "padded-zero-one" [([false,false,false],[true,false,false])] [true]
    check "one-one" [([true],[true])] [true]
    check "one-two" [([true],[false,true])] [false,true]
    check "padded-five" [([true,false,true,false],[true,false])] [true,true]
end DirectedFlowCutGap.InputWidthSmoke

def main := DirectedFlowCutGap.InputWidthSmoke.main
