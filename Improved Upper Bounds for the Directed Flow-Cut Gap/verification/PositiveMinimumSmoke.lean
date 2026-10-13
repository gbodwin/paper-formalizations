import DirectedFlowCutGap.OriginalMinimumPositive
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PositiveMinimumSmoke
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

def fractions : List (Bits × Bits) → Option (List BinaryRational.Fraction)
  | [] => some []
  | (num,den)::cs => if h : 0<value den then
      (fractions cs).map (⟨num,den,h⟩::·) else none

def pointers (heap : NaturalHeap) : ℕ → ℕ → Option (List (ℕ × ℕ))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair item tail) => do
      let .pair cost word ← heap[item]? | none
      let rest ← pointers heap fuel tail
      pure ((cost,word)::rest)
    | _ => none

def check (name : String) (vs : List Bits) (cs : List (Bits × Bits)) (chosen : Option ℕ) : IO Unit := do
  IO.println ("BEGIN actual positive minimum "++name)
  (←IO.getStdout).flush
  let some rows := fractions cs | throw (IO.userError "invalid fixture denominator")
  let vr := vertices vs PackedWordPairTable.seed
  let cr := costs cs vr
  let source := [true,false,true]
  let initial : BitState 256 := ⟨cr.heap,cr.next,⟨vr.root,cr.root,vr.root,cr.root⟩,[],254,source⟩
  let old := (eraseState initial).heap
  let items : List RetainedArgminProgram.Item :=
    (rows.filter fun q => !(isZero q.num).1).map fun q => ⟨q,0,0⟩
  let count := PositiveInventory.steps rows+RetainedArgminProgram.steps items+8
  let actual := execute PositiveMinimum.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let correct := match chosen with
    | none => heap[regs.d]?==some .nil
    | some i => match heap[regs.d]? with
      | some (.pair cost word) => some cost==itemAt old (value cr.root) i &&
          some word==itemAt old (value vr.root) i &&
          readDemand heap cost==cs[i]? && readBits heap (heap.length+1) word==vs[i]?
      | _ => false
  let W := cs.foldl (fun z q => max z (max q.1.length q.2.length)) 0
  let bound := PositiveMinimum.inputSteps rows W
  unless vs.length==cs.length && actual.halted && correct &&
      regs.a==value vr.root && regs.b==value cr.root && regs.c==value vr.root &&
      readVertices heap (heap.length+1) (value vr.root)==some vs &&
      readTable heap (heap.length+1) (value cr.root)==some cs &&
      heap.take cr.heap.length==old && actual.instructions==count && count≤bound &&
      actual.operations≤completeBound 256 (cr.heap.length+1) (cr.heap.length+1) bound &&
      actual.state.pc==255 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==cr.heap.length+PositiveInventory.cells rows+RetainedArgminProgram.cells items do
    throw (IO.userError ("FAIL actual positive minimum "++name))
  IO.println ("PASS actual positive minimum "++name++" instructions="++toString actual.instructions)

def main (args : List String) : IO Unit := do
  if args==["comparisons"] then
    check "first last" [[],[true],[false,true]] [([true],[true]),([],[true]),([true,true],[false,true])] (some 0)
    check "last smallest" [[],[true],[false,true]] [([true,true],[true]),([false,true],[true]),([true],[true])] (some 2)
    check "equal fractions first tie" [[false],[true,false]] [([true],[false,true]),([false,true],[false,false,true])] (some 0)
    check "padded fields second smaller" [[true,false,false],[false,true,false]] [([false,true,false],[true,false,false]),([true,false,false],[false,true,false])] (some 1)
    check "longer list" [[],[true],[false,true],[true,true]] [([],[true]),([true],[true]),([false,false],[true]),([false,true],[true])] (some 1)
    check "duplicate words distinct pointers" [[true],[true],[true]] [([true],[true]),([],[true]),([false,true],[true])] (some 0)
  else
    check "empty" [] [] none
    check "zero" [[]] [([],[true])] none
    check "padded zero" [[false,false]] [([false,false,false],[true,false])] none
    check "positive" [[true,false]] [([true,false],[false,true])] (some 0)
    check "all zero" [[],[true],[false,true]] [([],[true]),([false],[true]),([false,false],[false,true])] none
    check "middle only" [[],[true],[false,true]] [([],[true]),([true],[true]),([],[true])] (some 1)
end DirectedFlowCutGap.PositiveMinimumSmoke

def main := DirectedFlowCutGap.PositiveMinimumSmoke.main
