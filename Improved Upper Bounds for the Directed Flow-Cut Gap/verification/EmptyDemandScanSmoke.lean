import DirectedFlowCutGap.ActualEmptyDemandScan
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.EmptyDemandScanSmoke
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

def occurrence (heap : NaturalHeap) : ℕ → ℕ → Option ℕ
  | 0,p => do
      let .pair h _ ← heap[p]? | none
      pure h
  | i+1,p => do
      let .pair _ t ← heap[p]? | none
      occurrence heap i t

def check (name : String) (ds : List (Bits × Bits)) (rows : List Bits) (hit : Option ℕ) : IO Unit := do
  let table := PackedWordPairTable.construct ds
  let ar := vertices rows table
  let source := [true,false,true]
  let initial : BitState 160 := ⟨ar.heap,ar.next,⟨table.root,ar.root,table.root,ar.root⟩,[],158,source⟩
  let actual := execute EmptyDemandScan.program (EmptyDemandScan.steps rows ds+2) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let bound := EmptyDemandScan.inputSteps rows ds
  let correct := match hit with
    | none => heap[regs.d]?==some .nil
    | some i => occurrence (eraseState initial).heap i (value table.root)==some regs.d &&
        readDemand heap regs.d==ds[i]?
  unless actual.halted && correct &&
      readVertices heap (heap.length+1) regs.b==some rows && regs.a==value table.root &&
      readTable heap (heap.length+1) regs.a==some ds &&
      heap.take ar.heap.length==(eraseState initial).heap &&
      actual.instructions==EmptyDemandScan.steps rows ds+1 && actual.instructions≤bound &&
      actual.operations≤completeBound 160 (ar.heap.length+1) (ar.heap.length+1) bound &&
      actual.state.pc==159 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ar.heap.length+EmptyDemandScan.cells rows ds do
    throw (IO.userError ("FAIL actual empty-demand scan "++name))
  IO.println ("PASS actual empty-demand scan "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "empty-dim-zero" [] [] none
  check "empty-with-matrix" [] [[true]] none
  check "diagonal-first" [([],[])] [[false]] (some 0)
  check "padded-diagonal" [([],[false,false])] [[false]] (some 0)
  check "direct-first" [([],[true])] [[false,true],[false,false]] (some 0)
  check "reverse-rejected" [([true],[])] [[false,true],[false,false]] none
  check "all-absent" [([],[true]),([true],[])] [[false,false],[false,false]] none
  check "second-direct" [([true],[]),([],[true])] [[false,true],[false,false]] (some 1)
  check "second-diagonal" [([],[true]),([true],[true,false])] [[false,false],[false,false]] (some 1)
  check "first-retained-over-later" [([],[true]),([true],[true]),([],[true])] [[false,true],[false,false]] (some 0)
  check "duplicate-occurrence-first" [([],[true]),([],[true])] [[false,true],[false,false]] (some 0)
  check "third-padded-hit" [([],[true]),([true],[]),([false,false],[false,true])] [[false,false,true],[false,false,false],[false,false,false]] (some 2)
end DirectedFlowCutGap.EmptyDemandScanSmoke

def main := DirectedFlowCutGap.EmptyDemandScanSmoke.main
