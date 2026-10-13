import DirectedFlowCutGap.ScalarAdditionRowEncoding
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.ScalarAdditionRowSmoke
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

def check (name : String) (raw : List (Bits × Bits)) (scalar : Bits × Bits)
    (expected : List (Bits × Bits)) : IO Unit := do
  let some rows := fractions raw | throw (IO.userError "invalid row denominator")
  let some [sc] := fractions [scalar] | throw (IO.userError "invalid scalar denominator")
  let table := costs raw PackedWordPairTable.seed
  let sn := PackedWordPairTable.word scalar.1 table
  let sd := PackedWordPairTable.word scalar.2 sn
  let scalarHeap := PackedWordPairTable.allocate (.pair sn.root sd.root) sd
  let source := [true,false,true]
  let initial : BitState 160 :=
    ⟨scalarHeap.heap,scalarHeap.next,⟨table.root,scalarHeap.root,[],[]⟩,[],158,source⟩
  let old := (eraseState initial).heap
  let count := 1+ScalarAdditionRow.steps sc rows
  let actual := execute ScalarAdditionRow.program (count+1) initial
  let final := eraseState actual.state
  unless actual.halted && actual.instructions==count && actual.events==[] &&
      final.pc==159 && final.stack==[] && final.source==source &&
      readTable final.heap (final.heap.length+1) final.registers.d==some expected &&
      readTable final.heap (final.heap.length+1) (value table.root)==some raw &&
      readFraction final.heap (value scalarHeap.root)==some scalar &&
      final.registers.a==value table.root && final.registers.b==value scalarHeap.root &&
      final.registers.c==0 && final.heap.take old.length==old &&
      final.heap.length==old.length+ScalarAdditionRow.cells sc rows &&
      value actual.state.next==actual.state.heap.length &&
      actual.operations ≤ completeBound 160 (old.length+1) (old.length+1)
        (ScalarAdditionRow.inputSteps sc rows) do
    throw (IO.userError ("FAIL actual scalar addition row "++name++
      s!" result={readTable final.heap (final.heap.length+1) final.registers.d}"))
  IO.println ("PASS actual scalar addition row "++name++" steps="++toString actual.instructions)

def r (a b : ℕ) : Bits × Bits := (Nat.bits a,Nat.bits b)
def main (args : List String) : IO Unit := do
  match args.head?.getD "small" with
  | "small" =>
    check "empty" [] (r 1 2) []
    check "zeros" [r 0 1] (r 0 1) [r 0 1]
    check "ones" [r 1 1] (r 1 1) [r 2 1]
  | "middle" =>
    check "coprime" [r 1 2] (r 1 3) [r 5 6]
    check "zero-cost" [r 0 3] (r 1 2) [r 3 6]
    check "two-costs" [r 1 1,r 2 3] (r 1 2) [r 3 2,r 7 6]
  | "rows" =>
    check "zero-scalar" [r 1 2,r 0 1,r 3 4] (r 0 2) [r 2 4,r 0 2,r 6 8]
    check "duplicate" [r 1 2,r 1 2] (r 1 2) [r 4 4,r 4 4]
    check "unreduced" [r 2 3] (r 2 3) [r 12 9]
  | _ =>
    check "padded-zero" [([false,false],[true,false])] (r 0 3) [r 0 3]
    check "padded-both" [([false,true,false],[true,true,false])]
      ([true,false],[false,true,false]) [r 7 6]
    check "ordered" [r 3 2,r 1 2,r 3 2] (r 0 3) [r 9 6,r 3 6,r 9 6]
end DirectedFlowCutGap.ScalarAdditionRowSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.ScalarAdditionRowSmoke.main args
