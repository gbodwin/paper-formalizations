import DirectedFlowCutGap.ActualAvoidingDemandScan
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.AvoidingDemandScanSmoke
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

def check (name : String) (vs rows : List Bits) (cs ds : List (Bits × Bits))
    (expected : Option (ℕ × List (Bits × Bits))) : IO Unit := do
  IO.println ("BEGIN actual avoiding scan "++name)
  (←IO.getStdout).flush
  let vr := vertices vs PackedWordPairTable.seed
  let ar := vertices rows vr
  let cr := costs cs ar
  let dr := costs ds cr
  let detail := PackedWordPairTable.allocate (.pair cr.root ar.root) dr
  let ctx := PackedWordPairTable.allocate (.pair vr.root detail.root) detail
  let source := [true,false,true]
  let initial : BitState 1900 := ⟨ctx.heap,ctx.next,⟨dr.root,ctx.root,ar.root,vr.root⟩,[],1898,source⟩
  let count := AvoidingDemandScan.steps vs cs rows ds+1
  let actual := execute AvoidingDemandScan.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let correct := match expected with
    | none => heap[regs.d]?==some .nil
    | some (idx,es) => match heap[regs.d]? with
      | some (.pair demand path) => match heap[path]? with
        | some (.pair er qr) => some demand==itemAt (eraseState initial).heap (value dr.root) idx &&
          readDemand heap demand==ds[idx]? && readTable heap (heap.length+1) er==some es &&
          readDemand heap qr==some ([],[true])
        | _ => false
      | _ => false
  let W := vs.foldl (fun a x => max a x.length) 1
  let bound := AvoidingDemandScan.inputSteps vs cs rows ds W
  unless actual.halted && correct &&
      regs.a==value dr.root && regs.b==value ctx.root && regs.c==value ar.root &&
      readTable heap (heap.length+1) (value dr.root)==some ds &&
      readVertices heap (heap.length+1) (value vr.root)==some vs &&
      readVertices heap (heap.length+1) (value ar.root)==some rows &&
      readTable heap (heap.length+1) (value cr.root)==some cs &&
      heap.take ctx.heap.length==(eraseState initial).heap &&
      actual.instructions==count && count≤bound &&
      actual.operations≤completeBound 1900 (ctx.heap.length+1) (ctx.heap.length+1) bound &&
      actual.state.pc==1899 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ctx.heap.length+AvoidingDemandScan.cells vs cs rows ds do
    throw (IO.userError ("FAIL actual avoiding scan "++name))
  IO.println ("PASS actual avoiding scan "++name++" instructions="++toString actual.instructions)

def main (args : List String) : IO Unit := do
  if args==["pairs"] then
    check "first direct" [[],[true]] [[false,true],[false,false]] [([],[]),([false],[true])] [([],[true])] (some (0,[([],[true])]))
    check "late direct" [[],[true]] [[false,true],[false,false]] [([],[]),([],[true])] [([true],[]),([],[true])] (some (1,[([],[true])]))
    check "all absent" [[],[true]] [[false,false],[false,false]] [([true],[true]),([true],[true])] [([true],[]),([],[true])] none
    check "first before diagonal" [[],[true]] [[false,true],[false,false]] [([],[]),([],[])] [([],[true]),([],[])] (some (0,[([],[true])]))
    check "duplicate first" [[],[true]] [[false,true],[false,false]] [([],[]),([],[])] [([],[true]),([],[true])] (some (0,[([],[true])]))
  else if args==["removed"] then
    check "different endpoint masks" [[],[true],[false,true]] [[false,true,false],[false,false,true],[false,false,false]]
      [([true],[true]),([false,false],[true]),([true],[true])] [([],[false,true]),([],[true])]
      (some (1,[([],[true])]))
  else if args==["positive"] then
    check "positive interior retained" [[],[true],[false,true]] [[false,true,false],[false,false,true],[false,false,false]]
      [([],[]),([true],[true]),([],[])] [([],[false,true]),([],[true])] (some (0,[([],[true]),([true],[false,true])]))
  else
    check "empty graph" [] [] [] [] none
    check "no demands" [[]] [[false]] [([],[true])] [] none
    check "singleton" [[]] [[false]] [([],[true])] [([],[])] (some (0,[]))
    check "loop first" [[]] [[true]] [([],[])] [([],[]),([],[])] (some (0,[]))
    check "padded singleton" [[false,false]] [[false]] [([false,false],[false,true])] [([false,false],[false,false])] (some (0,[]))
end DirectedFlowCutGap.AvoidingDemandScanSmoke

def main := DirectedFlowCutGap.AvoidingDemandScanSmoke.main
