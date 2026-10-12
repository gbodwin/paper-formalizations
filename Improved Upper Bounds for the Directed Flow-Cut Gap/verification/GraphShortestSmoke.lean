import DirectedFlowCutGap.ActualGraphShortest
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.GraphShortestSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead BinaryRational
structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  instructions : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) : ℕ → BitState C → Trace C
  | 0,s => ⟨s,[],0,0,false⟩
  | fuel+1,s =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,[],a.operations,0,true⟩
      | some r =>
          let t := execute p fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.instructions+1,t.halted⟩

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none

def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | w::ws,s =>
    let t := wordList ws s
    let h := PackedWordPairTable.word w t
    PackedWordPairTable.allocate (.pair h.root t.root) h


def edges : List (Bits×Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | e::es,s =>
    let t := edges es s
    let u := PackedWordPairTable.word e.1 t
    let v := PackedWordPairTable.word e.2 u
    let edge := PackedWordPairTable.allocate (.pair u.root v.root) v
    PackedWordPairTable.allocate (.pair edge.root t.root) edge

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

def readFraction (heap : NaturalHeap) (p : ℕ) : Option (Bits×Bits) := do
  let some (.pair num den) := heap[p]? | none
  return (←readBits heap (heap.length+1) num,←readBits heap (heap.length+1) den)

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def padded : Fraction := ⟨[true,false,false],[false,true,false],by decide⟩

def check (name : String) (vertices adjacency : List Bits) (source target : Bits) (zeroCosts : Bool := false) : IO Unit := do
  IO.println ("BEGIN actual graph shortest "++name)
  (←IO.getStdout).flush
  let rows := (List.range adjacency.length).map fun i =>
    if zeroCosts then BinaryRational.zero else if i=1 then padded else frac (i+2) (i+3)
  let table := PackedWordPairTable.construct (rows.map fun x => (x.num,x.den))
  let matrix := wordList adjacency table
  let enumeration := wordList vertices matrix
  let sourceWord := PackedWordPairTable.word source enumeration
  let costContext := PackedWordPairTable.allocate (.pair table.root sourceWord.root) sourceWord
  let targetWord := PackedWordPairTable.word target costContext
  let mix := PackedWordPairTable.allocate (.pair matrix.root costContext.root) targetWord
  let bundle := PackedWordPairTable.allocate (.pair enumeration.root mix.root) mix
  let context := PackedWordPairTable.allocate (.pair targetWord.root bundle.root) bundle
  let initial : BitState 1344 := ⟨context.heap,context.next,
    ⟨enumeration.root,context.root,sourceWord.root,[]⟩,[],1342,[true,false,true]⟩
  let count := GraphRecoveryController.steps vertices adjacency rows source target source+1
  let cells := GraphRecoveryController.cells vertices adjacency rows source target source
  let actual := execute GraphRecoveryController.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let expected := GraphRecoveryController.result vertices adjacency rows source target source
  let correct := match expected with
    | none => heap[value actual.state.registers.d]?==some .nil
    | some q => match heap[value actual.state.registers.d]? with
      | some (.pair edgeRoot costRoot) =>
        readEdges heap (heap.length+1) edgeRoot==some q.edges &&
          readFraction heap costRoot==some (q.cost.num,q.cost.den)
      | _ => false
  unless actual.halted && actual.instructions==count && actual.state.pc==1343 && correct &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations ≤ completeBound 1344 (initial.heap.length+1) (initial.heap.length+1) count do
    throw (IO.userError ("FAILED actual graph shortest "++name++
      " steps="++toString actual.instructions++" expected="++toString count++
      " cells="++toString (actual.state.heap.length-initial.heap.length)++" expected="++toString cells))
  IO.println ("PASS actual graph shortest "++name++" steps="++toString count)
  (←IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args==["small"] then
    check "singleton-target" [[]] [[false]] [] []
    check "unreachable" [[],[true]] [[false,false],[false,false]] [] [true]
    check "direct-source-zero" [[],[true]] [[false,true],[false,false]] [] [true]
  else
    check "forward-chain" [[true],[],[false,true]]
      [[false,true,false],[false,false,true],[false,false,false]] [] [false,true]
    check "padded-labels" [[false,false],[true,false],[false,true,false]]
      [[false,true,false],[false,false,true],[false,false,false]] [false,false] [false,true,false]
    check "zero-cost-cycle-with-exit" [[],[true],[false,true]]
      [[false,true,false],[true,false,true],[false,false,false]] [] [false,true] true

end DirectedFlowCutGap.GraphShortestSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.GraphShortestSmoke.main args
