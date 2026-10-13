import DirectedFlowCutGap.ActualOriginalDispatch
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.OriginalDispatchSmoke
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

def itemAt (heap : NaturalHeap) : ℕ → ℕ → Option ℕ
  | p,0 => match heap[p]? with | some (.pair h _) => some h | _ => none
  | p,k+1 => match heap[p]? with | some (.pair _ t) => itemAt heap t k | _ => none

inductive Expected where
  | infeasible : ℕ → Expected
  | zero : Bits → Expected
  | positive : ℕ → List (Bits × Bits) → Expected

def check (name : String) (vs rows : List Bits) (cs ds : List (Bits × Bits)) (expected : Expected) : IO Unit := do
  IO.println ("BEGIN actual outer dispatch "++name)
  (←IO.getStdout).flush
  let vr := vertices vs PackedWordPairTable.seed
  let ar := vertices rows vr
  let cr := costs cs ar
  let dr := costs ds cr
  let detail := PackedWordPairTable.allocate (.pair cr.root ar.root) dr
  let ctx := PackedWordPairTable.allocate (.pair vr.root detail.root) detail
  let source := [true,false,true]
  let initial : BitState 2140 := ⟨ctx.heap,ctx.next,⟨dr.root,ctx.root,ar.root,vr.root⟩,[],2138,source⟩
  let count := OriginalDispatch.steps vs cs rows ds+1
  let actual := execute OriginalDispatch.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let correct := match heap[regs.d]? with
    | some (.pair tag payload) => match expected with
      | .infeasible idx => heap[tag]?==some (.flag false) &&
          some payload==itemAt (eraseState initial).heap (value dr.root) idx && readDemand heap payload==ds[idx]?
      | .zero flags => heap[tag]?==some (.flag true) && readBits heap (heap.length+1) payload==some flags
      | .positive idx es => heap[tag]?==some .nil && (match heap[payload]? with
        | some (.pair demand path) => match heap[path]? with
          | some (.pair er qr) => some demand==itemAt (eraseState initial).heap (value dr.root) idx &&
            readDemand heap demand==ds[idx]? && readTable heap (heap.length+1) er==some es &&
            readDemand heap qr==some ([],[true])
          | _ => false
        | _ => false)
    | _ => false
  let W := vs.foldl (fun a x => max a x.length) 1
  let bound := OriginalDispatch.inputSteps vs cs rows ds W
  unless actual.halted && correct &&
      regs.a==value dr.root && regs.b==value ctx.root && regs.c==value ar.root &&
      readTable heap (heap.length+1) (value dr.root)==some ds &&
      readVertices heap (heap.length+1) (value vr.root)==some vs &&
      readVertices heap (heap.length+1) (value ar.root)==some rows &&
      readTable heap (heap.length+1) (value cr.root)==some cs &&
      heap.take ctx.heap.length==(eraseState initial).heap &&
      actual.instructions==count && count≤bound &&
      actual.operations≤completeBound 2140 (ctx.heap.length+1) (ctx.heap.length+1) bound &&
      actual.state.pc==2139 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ctx.heap.length+OriginalDispatch.cells vs cs rows ds do
    throw (IO.userError ("FAIL actual outer dispatch "++name))
  IO.println ("PASS actual outer dispatch "++name++" instructions="++toString actual.instructions)

def main (args : List String) : IO Unit := do
  if args==["pairs"] then
    check "first direct" [[],[true]] [[false,true],[false,false]] [([],[]),([false],[true])] [([],[true])] (.infeasible 0)
    check "late direct" [[],[true]] [[false,true],[false,false]] [([],[]),([],[true])] [([true],[]),([],[true])] (.infeasible 1)
    check "all absent" [[],[true]] [[false,false],[false,false]] [([true],[true]),([true],[true])] [([true],[]),([],[true])] (.zero [false,false])
    check "padded reverse absent" [[false,false],[true,false]] [[false,true],[false,false]] [([false,false],[true]),([true],[true])] [([true,false],[false,false])] (.zero [true,false])
    check "duplicate first" [[],[true]] [[false,true],[false,false]] [([],[]),([],[])] [([],[true]),([],[true])] (.infeasible 0)
  else if args==["removed"] then
    check "zero interior cut" [[],[true],[false,true]] [[false,true,false],[false,false,true],[false,false,false]]
      [([true],[true]),([false,false],[true]),([true],[true])] [([],[false,true])] (.zero [false,true,false])
  else if args==["positive"] then
    check "positive interior witness" [[],[true],[false,true]] [[false,true,false],[false,false,true],[false,false,false]]
      [([],[]),([true],[true]),([],[])] [([],[false,true])] (.positive 0 [([],[true]),([true],[false,true])])
  else if args==["priority"] then
    check "global infeasibility priority" [[],[true],[false,true]] [[false,true,false],[false,false,true],[false,false,false]]
      [([true],[true]),([true],[true]),([true],[true])] [([],[false,true]),([true],[false,true])] (.infeasible 1)
  else
    check "empty graph" [] [] [] [] (.zero [])
    check "no demands" [[]] [[false]] [([],[true])] [] (.zero [true])
    check "singleton" [[]] [[false]] [([],[true])] [([],[])] (.infeasible 0)
    check "loop first" [[]] [[true]] [([],[])] [([],[]),([],[])] (.infeasible 0)
    check "padded singleton" [[false,false]] [[false]] [([false,false],[false,true])] [([false,false],[false,false])] (.infeasible 0)
end DirectedFlowCutGap.OriginalDispatchSmoke

def main := DirectedFlowCutGap.OriginalDispatchSmoke.main
