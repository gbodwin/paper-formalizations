import DirectedFlowCutGap.ShiftedGridRange
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.ShiftedGridSmoke
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


def readFraction (heap : NaturalHeap) (root : ℕ) : Option (Bits × Bits) := do
  let .pair n d ← heap[root]? | none
  return (← readBits heap (heap.length+1) n,← readBits heap (heap.length+1) d)

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

def check (name : String) (raw : List (Bits × Bits)) (index exponent : Bits) (expected : List (Bits × Bits)) : IO Unit := do
  let some rows := fractions raw | throw (IO.userError "invalid fixture denominator")
  unless value index<rows.length do throw (IO.userError "invalid fixture index")
  let table := costs raw PackedWordPairTable.seed
  let idx := PackedWordPairTable.word index table
  let exp := PackedWordPairTable.word exponent idx
  let source := [false,true,false]
  let initial : BitState 1220 := ⟨exp.heap,exp.next,⟨table.root,idx.root,exp.root,[]⟩,[],1218,source⟩
  let old := (eraseState initial).heap
  let count := ShiftedGridProgram.steps rows index exponent+1
  let actual := execute ShiftedGridProgram.program (count+1) initial
  let final := eraseState actual.state
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==1219 && final.stack==[] && final.source==source &&
      readTable final.heap (final.heap.length+1) final.registers.d==some expected &&
      readTable final.heap (final.heap.length+1) (value table.root)==some raw &&
      readBits final.heap (final.heap.length+1) (value idx.root)==some index &&
      readBits final.heap (final.heap.length+1) (value exp.root)==some exponent &&
      final.registers.a==value table.root && final.registers.b==value idx.root && final.registers.c==value exp.root &&
      final.heap.take old.length==old && final.heap.length==old.length+ShiftedGridProgram.cells rows index exponent &&
      value actual.state.next==actual.state.heap.length &&
      actual.operations ≤ completeBound 1220 (old.length+1) (old.length+1) (ShiftedGridProgram.inputSteps rows index exponent) &&
      value exponent ≤ LambdaGridProgram.gridLimit rows &&
      actual.operations ≤ completeBound 1220 (old.length+1) (old.length+1) (ShiftedGridProgram.gridInputSteps rows index exponent) do
    throw (IO.userError ("FAIL actual computed shifted row "++name++s!" result={readTable final.heap (final.heap.length+1) final.registers.d}"))
  IO.println ("PASS actual computed shifted row "++name++" steps="++toString actual.instructions)

def r (a b : ℕ) : Bits × Bits := (Nat.bits a,Nat.bits b)
def main (args : List String) : IO Unit := do
  match args.head?.getD "small" with
  | "small" =>
    check "zero-cost" [r 0 1] [] [] [r 0 1]
    check "one" [r 1 1] [] [] [r 2 1]
    check "half" [r 1 2] [] [] [r 4 4]
  | "middle" =>
    check "first" [r 2 3,r 7 2] [] (Nat.bits 1) [r 24 18,r 50 12]
    check "second" [r 5 1,r 3 2] (Nat.bits 1) [] [r 23 4,r 18 8]
    check "third" [r 1 1,r 2 1,r 5 2] (Nat.bits 2) (Nat.bits 1) [r 16 6,r 22 6,r 50 12]
  | "powers" =>
    check "zero-selected" [r 4 1,r 0 3] (Nat.bits 1) (Nat.bits 1) [r 24 6,r 0 18]
    check "fourth" [r 9 1,r 8 1,r 7 1,r 4 1] (Nat.bits 3) (Nat.bits 2) [r 52 4,r 48 4,r 44 4,r 32 4]
    check "duplicate" [r 2 3,r 2 3] (Nat.bits 1) [] [r 18 18,r 18 18]
  | _ =>
    check "padded-index" [r 1 1,r 1 2] [true,false,false] [true] [r 6 4,r 8 8]
    check "padded-cost" [([false,true,false],[true,true,false]),r 8 1,r 4 1] [] [false,true,false] [r 42 27,r 80 9,r 44 9]
    check "zero-cost-second" [r 1 1,r 0 2] [true,false] [false,true] [r 4 4,r 0 8]
end DirectedFlowCutGap.ShiftedGridSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.ShiftedGridSmoke.main args
