import DirectedFlowCutGap.SupportSearchAccounts
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.SupportRecoverySmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead SupportRecoveryProgram
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

def check (name : String) (vertices adjacency : List Bits) (supportEdges : List (Bits×Bits))
    (source target : Bits) : IO Unit := do
  IO.println ("BEGIN reconstructed support search "++name)
  (←IO.getStdout).flush
  let seed := PackedWordPairTable.construct []
  let matrix := wordList adjacency seed
  let supportList := edges supportEdges matrix
  let supportContext := PackedWordPairTable.allocate (.pair matrix.root supportList.root) supportList
  let enumeration := wordList vertices supportContext
  let targetWord := PackedWordPairTable.word target enumeration
  let bundle := PackedWordPairTable.allocate (.pair enumeration.root supportContext.root) targetWord
  let context := PackedWordPairTable.allocate (.pair targetWord.root bundle.root) bundle
  let sourceWord := PackedWordPairTable.word source context
  let initial : BitState 280 := ⟨sourceWord.heap,sourceWord.next,
    ⟨enumeration.root,context.root,sourceWord.root,[]⟩,[],270,[true,false,true]⟩
  let steps := searchSteps vertices adjacency supportEdges source target+1
  let cells := searchCells vertices adjacency supportEdges source target
  let actual := execute SupportRecoveryProgram.program (steps+1) initial
  let heap := (eraseState actual.state).heap
  unless actual.halted && actual.instructions==steps && actual.state.pc==279 &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      readEdges heap (heap.length+1) (value actual.state.registers.d)==
        some (search vertices adjacency supportEdges source target) &&
      actual.operations ≤ completeBound 280 (initial.heap.length+1) (initial.heap.length+1) steps do
    throw (IO.userError ("FAILED reconstructed support search "++name++
      " steps="++toString actual.instructions++" expected="++toString steps++
      " cells="++toString (actual.state.heap.length-initial.heap.length)++" expected="++toString cells))
  IO.println ("PASS reconstructed support search "++name++" steps="++toString steps)
  (←IO.getStdout).flush

def main : IO Unit := do
  check "empty-enumeration" [] [] [] [] []
  check "singleton-target" [[]] [[false]] [] [] []
  check "unreachable" [[],[true]] [[false,false],[false,false]] [] [] [true]
  check "direct" [[],[true]] [[false,true],[false,false]] [([],[true])] [] [true]
  check "missing-support" [[],[true]] [[false,true],[false,false]] [] [] [true]
  check "missing-adjacency" [[],[true]] [[false,false],[false,false]] [([],[true])] [] [true]
  check "forward-chain" [[true],[],[false,true]]
    [[false,true,false],[false,false,true],[false,false,false]]
    [([],[true]),([true],[false,true])] [] [false,true]
  check "padded-labels-and-support" [[false,false],[true,false],[false,true,false]]
    [[false,true,false],[false,false,true],[false,false,false]]
    [([false],[true]),([true,false,false],[false,true])] [false,false] [false,true,false]
  check "first-predecessor" [[],[true],[false,true],[true,true]]
    [[false,true,true,false],[false,false,false,true],[false,false,false,true],[false,false,false,false]]
    [([],[true]),([],[false,true]),([true],[true,true]),([false,true],[true,true])] [] [true,true]
  check "cycle-with-exit" [[],[true],[false,true]]
    [[false,true,false],[true,false,true],[false,false,false]]
    [([],[true]),([true],[]),([true],[false,true])] [] [false,true]

end DirectedFlowCutGap.SupportRecoverySmoke

def main : IO Unit := DirectedFlowCutGap.SupportRecoverySmoke.main
