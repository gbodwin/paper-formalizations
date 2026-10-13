import DirectedFlowCutGap.ActualMinimumShift
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.MinimumShiftSmoke
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

def check (name : String) (raw : List (Bits × Bits)) (exponent : Bits)
    (chosen : Option ℕ) (expected : Option (List (Bits × Bits))) : IO Unit := do
  IO.println ("BEGIN actual minimum shifted row "++name)
  (←IO.getStdout).flush
  let some rows := fractions raw | throw (IO.userError "invalid fixture denominator")
  let table := costs raw PackedWordPairTable.seed
  let exp := PackedWordPairTable.word exponent table
  let source := [false,true,false]
  let initial : BitState 1560 := ⟨exp.heap,exp.next,⟨table.root,[],exp.root,[]⟩,[],1558,source⟩
  let old := (eraseState initial).heap
  let items : List RetainedArgminProgram.Item :=
    (rows.filter fun q => !(isZero q.num).1).map fun q => ⟨q,0,0⟩
  let minCount := RowVertexScan.steps rows.length []+4*rows.length+9+
    PositiveInventory.steps rows+RetainedArgminProgram.steps items+16
  let count := match chosen with
    | none => minCount+5
    | some i => minCount+ShiftedGridProgram.steps rows (Nat.bits i) exponent+9
  let actual := execute MinimumShift.program (count+1) initial
  let final := eraseState actual.state
  let correct := match expected with
    | none => final.heap[final.registers.d]?==some .nil
    | some want => readTable final.heap (final.heap.length+1) final.registers.d==some want
  unless actual.halted && actual.instructions==count && actual.events==[] && correct &&
      final.pc==1559 && final.stack==[] && final.source==source &&
      readTable final.heap (final.heap.length+1) (value table.root)==some raw &&
      readBits final.heap (final.heap.length+1) (value exp.root)==some exponent &&
      final.registers.a==value table.root && final.registers.b==0 && final.registers.c==value exp.root &&
      final.heap.take old.length==old && value actual.state.next==actual.state.heap.length &&
      actual.instructions ≤ MinimumShift.inputSteps rows exponent &&
      actual.operations ≤ completeBound 1560 (old.length+1) (old.length+1) (MinimumShift.inputSteps rows exponent) do
    throw (IO.userError ("FAIL actual minimum shifted row "++name++s!" result={readTable final.heap (final.heap.length+1) final.registers.d} count={actual.instructions}/{count}"))
  IO.println ("PASS actual minimum shifted row "++name++" steps="++toString actual.instructions)

def r (a b : ℕ) : Bits × Bits := (Nat.bits a,Nat.bits b)
def main (args : List String) : IO Unit := do
  match args.head?.getD "small" with
  | "small" =>
    check "empty" [] [] none none
    check "all-zero" [r 0 1,r 0 3] [] none none
    check "one" [r 1 1] [] (some 0) (some [r 2 1])
  | "pairs" =>
    check "half" [r 1 2] [] (some 0) (some [r 4 4])
    check "first-minimum" [r 1 1,r 2 1] [] (some 0) (some [r 3 2,r 5 2])
    check "second-minimum" [r 2 1,r 1 1] [] (some 1) (some [r 5 2,r 3 2])
  | "ties" =>
    check "skip-zero" [r 0 1,r 1 1] [] (some 1) (some [r 1 2,r 3 2])
    check "equal-fraction-tie" [r 1 2,r 2 4] [] (some 0) (some [r 6 8,r 12 16])
    check "unreduced-zero" [r 0 3,r 1 1,r 2 1] [true] (some 1) (some [r 6 9,r 5 3,r 8 3])
  | _ =>
    check "padded-exponent" [r 2 2,r 1 2] [false,false] (some 1) (some [r 10 8,r 6 8])
    check "padded-all-zero" [([false,false],[true,false]),r 0 3] [true] none none
    check "last-minimum-power" [r 3 1,r 2 1,r 1 1] [false,true] (some 2) (some [r 13 3,r 10 3,r 7 3])
end DirectedFlowCutGap.MinimumShiftSmoke

def main := DirectedFlowCutGap.MinimumShiftSmoke.main
