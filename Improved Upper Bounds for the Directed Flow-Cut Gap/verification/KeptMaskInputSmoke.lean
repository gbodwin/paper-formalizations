import DirectedFlowCutGap.ActualKeptMaskInput
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.KeptMaskInputSmoke
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


def vertices : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | u::us,s =>
    let tail := vertices us s
    let head := PackedWordPairTable.word u tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

def readVertices (heap : NaturalHeap) : ℕ → ℕ → Option (List Bits)
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair h t) => do
      let u ← readBits heap (heap.length+1) h
      let us ← readVertices heap fuel t
      pure (u::us)
    | _ => none

def rows : List (Bits × Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | r::rs,s => PackedWordPairTable.prepend r (rows rs s)

def check (name : String) (s t : Bits) (vs : List Bits) (cs : List (Bits × Bits)) (expected : Bits) : IO Unit := do
  let sr := PackedWordPairTable.word s PackedWordPairTable.seed
  let tr := PackedWordPairTable.word t sr
  let vr := vertices vs tr
  let rr := rows cs vr
  let ep := PackedWordPairTable.allocate (.pair sr.root tr.root) rr
  let ctx := PackedWordPairTable.allocate (.pair ep.root rr.root) ep
  let source := [true,false,true]
  let initial : BitState 200 := ⟨ctx.heap,ctx.next,⟨vr.root,ctx.root,vr.root,ctx.root⟩,[],198,source⟩
  let actual := execute KeptMaskInput.program (KeptMaskInput.steps s t vs cs+2) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let bound := KeptMaskInput.inputSteps s t vs cs
  unless actual.halted && readBits heap (heap.length+1) regs.d==some expected &&
      readVertices heap (heap.length+1) regs.a==some vs && regs.b==value ctx.root &&
      heap.take ctx.heap.length==(eraseState initial).heap &&
      readBits heap (heap.length+1) (value sr.root)==some s &&
      readBits heap (heap.length+1) (value tr.root)==some t &&
      actual.instructions==KeptMaskInput.steps s t vs cs+1 && actual.instructions≤bound &&
      actual.operations≤completeBound 200 (ctx.heap.length+1) (ctx.heap.length+1) bound &&
      actual.state.pc==199 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ctx.heap.length+KeptMaskInput.cells s t vs cs do
    throw (IO.userError ("FAIL actual original kept mask "++name))
  IO.println ("PASS actual original kept mask "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "empty" [] [true] [] [] []
  check "nonzero" [] [true] [[true,true]] [([true],[])] [true]
  check "source-padded" [false,false] [true] [[]] [([false,false],[true])] [true]
  check "target-padded" [] [true] [[true,false]] [([],[true,false])] [true]
  check "neither" [] [true] [[false,true]] [([false],[])] [false]
  check "mixed-order" [] [true] [[],[true],[false,true]] [([],[]),([false],[true]),([false,false],[])] [true,true,false]
  check "nonzero-exception" [] [true] [[false,true],[],[true,true]] [([false,true],[]),([],[false]),([false],[])] [true,true,false]
  check "duplicates" [true] [true,false] [[true,false],[false],[true]] [([],[true]),([],[true]),([true],[false])] [true,false,true]

end DirectedFlowCutGap.KeptMaskInputSmoke

def main := DirectedFlowCutGap.KeptMaskInputSmoke.main
