import DirectedFlowCutGap.GraphRelaxationExecution
import DirectedFlowCutGap.GraphRelaxationRefinement
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.GraphRelaxationSmoke
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open GraphWalkExtension GraphRelaxationProgram
structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) : ℕ → BitState C → Trace C
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,[],a.operations,true⟩
      | some r =>
          let t := execute p fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.halted⟩

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none

def readFraction (heap : NaturalHeap) (p : ℕ) : Option (Bits×Bits) := do
  let some (.pair num den) := heap[p]? | none
  return (←readBits heap (heap.length+1) num,←readBits heap (heap.length+1) den)

def checkCommon {C : ℕ} (name : String) (initial : BitState C) (t : Trace C) (steps cells : ℕ) : IO Unit := do
  unless t.halted && t.events.isEmpty && t.state.source==initial.source &&
      t.state.stack.isEmpty && t.state.heap.take initial.heap.length==initial.heap &&
      t.state.heap.length==initial.heap.length+cells &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ completeBound C (initial.heap.length+1) (initial.heap.length+1) steps do
    throw (IO.userError ("FAILED graph-relaxation machine invariants: "++name))

def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | w::ws,s =>
    let t := wordList ws s
    let h := PackedWordPairTable.word w t
    PackedWordPairTable.allocate (.pair h.root t.root) h


def fraction (q : Fraction) (s : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let n := PackedWordPairTable.word q.num s
  let d := PackedWordPairTable.word q.den n
  PackedWordPairTable.allocate (.pair n.root d.root) d

def edges : List (Bits×Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | e::es,s =>
    let t := edges es s
    let u := PackedWordPairTable.word e.1 t
    let v := PackedWordPairTable.word e.2 u
    let edge := PackedWordPairTable.allocate (.pair u.root v.root) v
    PackedWordPairTable.allocate (.pair edge.root t.root) edge

def prepare : List Entry → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | x::xs,s =>
    let t := prepare xs s
    let es := edges x.2.edges t
    let q := fraction x.2.cost es
    let walk := PackedWordPairTable.allocate (.pair es.root q.root) q
    let v := PackedWordPairTable.word x.1 walk
    let entry := PackedWordPairTable.allocate (.pair v.root walk.root) v
    PackedWordPairTable.allocate (.pair entry.root t.root) entry

def readEdges (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits×Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      let some (.pair a b) := heap[head]? | none
      let u ← readBits heap (heap.length+1) a
      let v ← readBits heap (heap.length+1) b
      let es ← readEdges heap fuel tail
      return (u,v)::es
    | _ => none

def observe (q : Walk) : List (Bits×Bits) × (Bits×Bits) := (q.edges,(q.cost.num,q.cost.den))
def readWalk (heap : NaturalHeap) (p : ℕ) : Option (List (Bits×Bits) × (Bits×Bits)) := do
  let some (.pair es cost) := heap[p]? | none
  return (←readEdges heap (heap.length+1) es,←readFraction heap cost)

def check (name : String) (adj : List Bits) (rows : List Fraction) (sw u : Bits) (xs : List Entry) : IO Unit := do
  let table := PackedWordPairTable.construct (rows.map fun q => (q.num,q.den))
  let src := PackedWordPairTable.word sw table
  let cost := PackedWordPairTable.allocate (.pair table.root src.root) src
  let matrix := wordList adj cost
  let mix := PackedWordPairTable.allocate (.pair matrix.root cost.root) matrix
  let vertex := PackedWordPairTable.word u mix
  let context := PackedWordPairTable.allocate (.pair vertex.root mix.root) vertex
  let built := prepare xs context
  let initial : BitState 532 := ⟨built.heap,built.next,⟨built.root,context.root,[],[]⟩,[],530,[true,false,true]⟩
  let steps := GraphRelaxationProgram.steps adj rows sw u xs+1
  let t := execute GraphRelaxationProgram.program (steps+1) initial
  checkCommon name initial t steps (GraphRelaxationProgram.cells adj rows sw u xs)
  let heap := (eraseState t.state).heap
  let expected := GraphRelaxationProgram.scan adj rows sw u xs
  let correct := match expected with
    | none => heap[value t.state.registers.d]?==some .nil
    | some q => readWalk heap (value t.state.registers.d)==some (observe q)
  unless t.state.pc==531 && correct do throw (IO.userError ("FAILED actual graph scan: "++name))
  IO.println ("PASS actual graph relaxation "++name)

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def entry (v score tag : ℕ) : Entry :=
  (v.bits,⟨[(tag.bits,v.bits)],frac score 0⟩)
def rows : List Fraction := [frac 3 1,frac 1 0,frac 2 0]
def allEdges : List Bits := List.replicate 3 (List.replicate 3 true)
def noEdges : List Bits := List.replicate 3 (List.replicate 3 false)
def main : IO Unit := do
  check "empty old table" noEdges rows [] [] []
  check "all absent" noEdges rows [] [] [entry 1 2 7,entry 2 1 8]
  check "one accepted edge" allEdges rows (2:ℕ).bits [] [entry 1 2 7]
  check "first lower cost" allEdges rows (2:ℕ).bits [] [entry 1 1 7,entry 2 3 8]
  check "later lower cost" allEdges rows (2:ℕ).bits [] [entry 1 3 7,entry 2 1 8]
  check "first equal cost retained" allEdges rows (2:ℕ).bits [] [entry 1 1 7,entry 2 1 8]
  check "source-zero row" allEdges rows [] [] [entry 1 2 7,entry 2 1 8]
  check "skipped head" [[false,false,true],[false,false,false],[false,false,false]] rows (2:ℕ).bits []
    [entry 1 0 7,entry 2 5 8]
  check "skipped tail" [[false,true,false],[false,false,false],[false,false,false]] rows (2:ℕ).bits []
    [entry 1 5 7,entry 2 0 8]
  check "padded zero source and vertex" allEdges rows [false,false] [false]
    [([true,false],⟨[],frac 1 0⟩),([false,true,false],⟨[],frac 2 0⟩)]
  check "positive row and canonical fraction" allEdges rows (2:ℕ).bits []
    [((1:ℕ).bits,⟨[],frac 1 2⟩),((2:ℕ).bits,⟨[],frac 2 5⟩)]
  IO.println "GRAPH_RELAXATION_ACTUAL_FIXTURES passed: 11 cases"
end DirectedFlowCutGap.GraphRelaxationSmoke

def main : IO Unit := DirectedFlowCutGap.GraphRelaxationSmoke.main
