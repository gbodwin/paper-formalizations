import DirectedFlowCutGap.DemandCollectionProgram
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.DemandCollectionSmoke
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

def demands : List (Bits×Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared×List DemandCollection.Demand
  | [],s => (PackedWordPairTable.allocate .nil s,[])
  | (sw,tw)::ds,s =>
    let (tail,xs) := demands ds s
    let a := PackedWordPairTable.word sw tail
    let b := PackedWordPairTable.word tw a
    let r := PackedWordPairTable.allocate (.pair a.root b.root) b
    let node := PackedWordPairTable.allocate (.pair r.root tail.root) r
    (node,⟨sw,tw,value r.root,value node.root⟩::xs)

def check (name : String) (vertices adjacency : List Bits) (ds : List (Bits×Bits))
    (zeroCosts : Bool := false) : IO Unit := do
  IO.println ("BEGIN actual demand collector "++name)
  (←IO.getStdout).flush
  let rows := (List.range adjacency.length).map fun i =>
    if zeroCosts then BinaryRational.zero else if i=1 then padded else frac (i+2) (i+3)
  let table := PackedWordPairTable.construct (rows.map fun x => (x.num,x.den))
  let matrix := wordList adjacency table
  let enumeration := wordList vertices matrix
  let bundle := PackedWordPairTable.allocate (.pair matrix.root table.root) enumeration
  let shared := PackedWordPairTable.allocate (.pair enumeration.root bundle.root) bundle
  let (dsInput,xs) := demands ds shared
  let initial : BitState 1604 := ⟨dsInput.heap,dsInput.next,⟨dsInput.root,shared.root,[],[]⟩,[],1600,[true,false,true]⟩
  let records := DemandCollection.records vertices adjacency rows (value initial.next) xs
  let items := records.map DemandCollection.Record.item
  let count := DemandCollection.steps vertices adjacency rows xs+2+RetainedArgminProgram.steps items
  let cells := DemandCollection.cells vertices adjacency rows xs+RetainedArgminProgram.cells items
  let actual := execute DemandCollection.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let expected := RetainedArgminProgram.select items
  let correct := match expected with
    | none => heap[value actual.state.registers.d]?==some .nil
    | some item => value actual.state.registers.d==item.address
  let recordsCorrect := records.all fun z => match heap[z.item.address]?,heap[z.item.payload]? with
    | some (.pair score payload),some (.pair occurrence path) =>
      payload==z.item.payload && occurrence==z.demand.occurrence &&
      readFraction heap score==some (z.path.cost.num,z.path.cost.den) &&
      match heap[path]? with
      | some (.pair es cost) => readEdges heap (heap.length+1) es==some z.path.edges &&
          readFraction heap cost==some (z.path.cost.num,z.path.cost.den)
      | _ => false
    | _,_ => false
  unless actual.halted && actual.instructions==count && correct && recordsCorrect &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations ≤ completeBound 1604 (initial.heap.length+1) (initial.heap.length+1) count do
    throw (IO.userError ("FAILED demand collector "++name++
      " steps="++toString actual.instructions++" expected="++toString count++
      " cells="++toString (actual.state.heap.length-initial.heap.length)++" expected="++toString cells))
  IO.println ("PASS actual demand collector "++name++" steps="++toString count++" candidates="++toString records.length)
  (←IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args==["small"] then
    check "no-demands" [[]] [[false]] []
    check "singleton-self" [[]] [[false]] [([],[])]
    check "all-unreachable" [[],[true]] [[false,false],[false,false]] [([],[true]),([true],[])]
    check "source-zero-first-tie" [[],[true]] [[false,true],[false,false]] [([],[true]),([],[])]
  else if args==["chain"] then
    check "unreachable-then-chain" [[],[true],[false,true]]
      [[false,true,false],[false,false,true],[false,false,false]] [([false,true],[]),([],[false,true])]
  else if args==["duplicate"] then
    check "duplicate-occurrences" [[],[true],[false,true]]
      [[false,true,false],[false,false,true],[false,false,false]] [([],[false,true]),([],[false,true])]
  else if args==["padded"] then
    check "padded-labels" [[false,false],[true,false],[false,true,false]]
      [[false,true,false],[false,false,true],[false,false,false]] [([false,false],[false,true,false])]
  else if args==["cycle"] then
    check "zero-cycle-first-tie" [[],[true],[false,true]]
      [[false,true,false],[true,false,true],[false,false,false]] [([],[false,true]),([true],[false,true])] true

end DirectedFlowCutGap.DemandCollectionSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.DemandCollectionSmoke.main args
