import DirectedFlowCutGap.ActualGraphDiscovery
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.GraphDiscoverySmoke
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open GraphWalkExtension GraphDiscoveryProgram
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
    throw (IO.userError ("FAILED graph-discovery machine invariants: "++name))

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

def check (name : String) (vertices adj : List Bits) (rows : List Fraction) (sw target u : Bits) : IO Unit := do
  IO.println ("BEGIN actual graph discovery "++name)
  (← IO.getStdout).flush
  let table := PackedWordPairTable.construct (rows.map fun q => (q.num,q.den))
  let src := PackedWordPairTable.word sw table
  let cost := PackedWordPairTable.allocate (.pair table.root src.root) src
  let matrix := wordList adj cost
  let mix := PackedWordPairTable.allocate (.pair matrix.root cost.root) matrix
  let enumeration := wordList vertices mix
  let targetWord := PackedWordPairTable.word target enumeration
  let bundle := PackedWordPairTable.allocate (.pair enumeration.root mix.root) targetWord
  let context := PackedWordPairTable.allocate (.pair targetWord.root bundle.root) bundle
  let input := PackedWordPairTable.word u context
  let initial : BitState 720 := ⟨input.heap,input.next,⟨enumeration.root,context.root,input.root,[]⟩,[],717,[true,false,true]⟩
  let steps := minimizeSteps vertices adj rows sw target u+1
  let t := execute GraphDiscoveryProgram.program (steps+1) initial
  checkCommon name initial t steps (minimizeCells vertices adj rows sw target u)
  let heap := (eraseState t.state).heap
  let expected := minimize vertices adj rows sw target u
  let correct := match expected with
    | none => heap[value t.state.registers.d]?==some .nil
    | some q => readWalk heap (value t.state.registers.d)==some (observe q)
  unless t.state.pc==719 && correct do throw (IO.userError ("FAILED actual graph discovery: "++name))
  IO.println ("PASS actual graph discovery "++name++" steps="++toString steps)
  (← IO.getStdout).flush

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩

def main : IO Unit := do
  check "singleton-target" [[]] [[false]] [frac 5 0] [] [] []
  check "unreachable" [[],[true]] [[false,false],[false,false]] [frac 5 0,frac 7 0] [] [true] []
  check "direct-source-zero" [[],[true]] [[false,true],[false,false]] [frac 5 0,frac 7 0] [] [true] []
  check "two-edge-fraction" [[],[true],[false,true]]
    [[false,true,false],[false,false,true],[false,false,false]] [frac 5 0,frac 2 2,frac 7 0] [] [false,true] []
  check "cycle-with-exit" [[],[true],[false,true]]
    [[false,true,false],[true,false,true],[false,false,false]] [frac 5 0,frac 2 0,frac 7 0] [] [false,true] []
  check "padded-labels" [[false,false],[true,false],[false,true,false]]
    [[false,true,false],[false,false,true],[false,false,false]] [frac 5 0,frac 2 0,frac 7 0]
    [false,false,false] [false,true,false] [false,false]
  check "first-tie" [[],[true],[false,true],[true,true]]
    [[false,true,true,false],[false,false,false,true],[false,false,false,true],[false,false,false,false]]
    [frac 5 0,frac 2 0,frac 2 0,frac 7 0] [] [true,true] []
  check "reordered-first-tie" [[],[false,true],[true],[true,true]]
    [[false,true,true,false],[false,false,false,true],[false,false,false,true],[false,false,false,false]]
    [frac 5 0,frac 2 0,frac 2 0,frac 7 0] [] [true,true] []

end DirectedFlowCutGap.GraphDiscoverySmoke

def main : IO Unit := DirectedFlowCutGap.GraphDiscoverySmoke.main
