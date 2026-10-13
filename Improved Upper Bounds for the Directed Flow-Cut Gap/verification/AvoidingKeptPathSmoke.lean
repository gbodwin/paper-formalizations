import DirectedFlowCutGap.ActualAvoidingKeptPath
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.AvoidingKeptPathSmoke
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

def costs : List (Bits × Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | r::rs,s => PackedWordPairTable.prepend r (costs rs s)

def check (name : String) (vs rows : List Bits) (cs : List (Bits × Bits)) (sw target : Bits)
    (expected : Option (List (Bits × Bits))) : IO Unit := do
  IO.println ("BEGIN actual avoiding path "++name)
  (←IO.getStdout).flush
  let vr := vertices vs PackedWordPairTable.seed
  let ar := vertices rows vr
  let cr := costs cs ar
  let sr := PackedWordPairTable.word sw cr
  let tr := PackedWordPairTable.word target sr
  let ep := PackedWordPairTable.allocate (.pair sr.root tr.root) tr
  let mc := PackedWordPairTable.allocate (.pair ep.root cr.root) ep
  let ctx := PackedWordPairTable.allocate (.pair mc.root ar.root) mc
  let source := [true,false,true]
  let initial : BitState 1800 := ⟨ctx.heap,ctx.next,⟨vr.root,ctx.root,ar.root,ep.root⟩,[],1798,source⟩
  let count := AvoidingKeptPath.steps sw target vs cs rows+1
  let actual := execute AvoidingKeptPath.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let correct := match expected with
    | none => heap[regs.d]?==some .nil
    | some es => match heap[regs.d]? with
      | some (.pair er qr) => readTable heap (heap.length+1) er==some es && readDemand heap qr==some ([],[true])
      | _ => false
  let W := vs.foldl (fun a x => max a x.length) 1
  let bound := AvoidingKeptPath.inputSteps sw target vs cs rows W
  unless actual.halted && correct &&
      regs.a==value vr.root && regs.b==value ctx.root && regs.c==value ar.root &&
      readVertices heap (heap.length+1) (value vr.root)==some vs &&
      readVertices heap (heap.length+1) (value ar.root)==some rows &&
      readTable heap (heap.length+1) (value cr.root)==some cs &&
      heap.take ctx.heap.length==(eraseState initial).heap &&
      actual.instructions==count && count≤bound &&
      actual.operations≤completeBound 1800 (ctx.heap.length+1) (ctx.heap.length+1) bound &&
      actual.state.pc==1799 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ctx.heap.length+AvoidingKeptPath.cells sw target vs cs rows do
    throw (IO.userError ("FAIL actual avoiding path "++name))
  IO.println ("PASS actual avoiding path "++name++" instructions="++toString actual.instructions)

def main (args : List String) : IO Unit := do
  if args==["pairs"] then
    check "zero-cost endpoints" [[],[true]] [[false,true],[false,false]] [([],[]),([false],[true])] [] [true] (some [([],[true])])
    check "reverse absent" [[],[true]] [[false,true],[false,false]] [([true],[true]),([true],[true])] [true] [] none
    check "padded endpoints" [[false,false],[true,false]] [[false,true],[false,false]] [([false,false],[]),([],[true,false])] [false,false] [true,false] (some [([false,false],[true,false])])
  else if args==["removed"] then
    check "zero interior removed" [[],[true],[false,true]] [[false,true,false],[false,false,true],[false,false,false]]
      [([true],[true]),([false,false],[true]),([true],[true])] [] [false,true] none
  else if args==["positive"] then
    check "positive interior retained" [[],[true],[false,true]] [[false,true,false],[false,false,true],[false,false,false]]
      [([],[]),([true],[true]),([],[])] [] [false,true] (some [([],[true]),([true],[false,true])])
  else
    check "singleton" [[]] [[false]] [([],[true])] [] [] (some [])
    check "loop" [[]] [[true]] [([],[])] [] [] (some [])
    check "padded singleton" [[false,false]] [[false]] [([false,false],[false,true])] [false,false] [false,false] (some [])
end DirectedFlowCutGap.AvoidingKeptPathSmoke

def main := DirectedFlowCutGap.AvoidingKeptPathSmoke.main
