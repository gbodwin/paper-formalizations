import DirectedFlowCutGap.ActualAvoidingZeroContext
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.AvoidingZeroContextSmoke
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

def readDemand (heap : NaturalHeap) (p : ℕ) : Option (Bits × Bits) := do
  let .pair a b ← heap[p]? | none
  let u ← readBits heap (heap.length+1) a
  let v ← readBits heap (heap.length+1) b
  pure (u,v)

def readTable (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits × Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair h t) => do
      let e ← readDemand heap h
      let es ← readTable heap fuel t
      pure (e::es)
    | _ => none

def readGlobal (heap : NaturalHeap) (root : ℕ) : Option (List Bits × List Bits × List (Bits × Bits) × Bits × Bits) := do
  let .pair tr bundle ← heap[root]? | none
  let .pair vr mix ← heap[bundle]? | none
  let .pair ar cost ← heap[mix]? | none
  let .pair row sr ← heap[cost]? | none
  let vs ← readVertices heap (heap.length+1) vr
  let adjacency ← readVertices heap (heap.length+1) ar
  let rows ← readTable heap (heap.length+1) row
  let sw ← readBits heap (heap.length+1) sr
  let target ← readBits heap (heap.length+1) tr
  pure (vs,adjacency,rows,sw,target)

def check (name : String) (vs rows : List Bits) (sw target : Bits) : IO Unit := do
  let vr := vertices vs PackedWordPairTable.seed
  let ar := vertices rows vr
  let sr := PackedWordPairTable.word sw ar
  let tr := PackedWordPairTable.word target sr
  let ep := PackedWordPairTable.allocate (.pair sr.root tr.root) tr
  let ctx := PackedWordPairTable.allocate (.pair ar.root ep.root) ep
  let source := [true,false,true]
  let initial : BitState 64 := ⟨ctx.heap,ctx.next,⟨vr.root,ctx.root,ar.root,ep.root⟩,[],62,source⟩
  let count := AvoidingZeroContext.inputSteps vs
  let actual := execute AvoidingZeroContext.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  unless actual.halted && readGlobal heap regs.d==some (vs,rows,List.replicate vs.length ([],[true]),sw,target) &&
      regs.a==value vr.root && regs.b==value ctx.root && regs.c==value ar.root &&
      heap.take ctx.heap.length==(eraseState initial).heap &&
      actual.instructions==count &&
      actual.operations≤completeBound 64 (ctx.heap.length+1) (ctx.heap.length+1) count &&
      actual.state.pc==63 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ctx.heap.length+vs.length+14 do
    throw (IO.userError ("FAIL actual zero graph context "++name))
  IO.println ("PASS actual zero graph context "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "empty" [] [] [] []
  check "singleton" [[]] [[false]] [] []
  check "loop" [[]] [[true]] [] []
  check "directed" [[],[true]] [[false,true],[false,false]] [] [true]
  check "reverse" [[],[true]] [[false,true],[false,false]] [true] []
  check "chain" [[],[true],[false,true]] [[false,true,false],[false,false,true],[false,false,false]] [] [false,true]
  check "padded-labels" [[false,false],[true,false]] [[false,true],[false,false]] [false,false] [true,false]
  check "padded-empty" [] [] [false,false] [false,false,false]
end DirectedFlowCutGap.AvoidingZeroContextSmoke

def main := DirectedFlowCutGap.AvoidingZeroContextSmoke.main
