import DirectedFlowCutGap.GraphOracleProgram
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.GraphOracleSmoke
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
    (expectedMask : Bits) (expectedVertex : ℕ) (zeroCosts : Bool := false) : IO Unit := do
  IO.println ("BEGIN actual full oracle "++name)
  (←IO.getStdout).flush
  let rows := (List.range adjacency.length).map fun i =>
    if zeroCosts then BinaryRational.zero else if i=1 then padded else frac (i+2) (i+3)
  let caps := (List.range vertices.length).map fun i => frac (vertices.length-i) 0
  let table := PackedWordPairTable.construct (rows.map fun x => (x.num,x.den))
  let matrix := wordList adjacency table
  let enumeration := wordList vertices matrix
  let bundle := PackedWordPairTable.allocate (.pair matrix.root table.root) enumeration
  let shared := PackedWordPairTable.allocate (.pair enumeration.root bundle.root) bundle
  let capacity := caps.foldr (fun q tail =>
    let num := PackedWordPairTable.word q.num tail
    let den := PackedWordPairTable.word q.den num
    let record := PackedWordPairTable.allocate (.pair num.root den.root) den
    PackedWordPairTable.allocate (.pair record.root tail.root) record) (PackedWordPairTable.allocate .nil shared)
  let post := PackedWordPairTable.allocate (.pair enumeration.root capacity.root) capacity
  let context := PackedWordPairTable.allocate (.pair shared.root post.root) post
  let (dsInput,xs) := demands ds context
  let initial : BitState 2120 := ⟨dsInput.heap,dsInput.next,⟨dsInput.root,context.root,[],[]⟩,[],2100,[true,false,true]⟩
  let dnext := value initial.next+1
  let records := DemandCollection.records vertices adjacency rows dnext xs
  let chosen := (BinaryFractionalGraphOracle.argmin DemandCollection.recordScore records).1
  let dcells := DemandCollection.selectedCells vertices adjacency rows dnext xs
  let dsteps := DemandCollection.selectedSteps vertices adjacency rows dnext xs
  let pnext := dnext+dcells
  let (psteps,pcells) := match chosen with
    | none => (6*(vertices.length-1)+15,2*(vertices.length-1)+5)
    | some z =>
      let mask := OracleMask.mask z.demand.sourceWord z.demand.targetWord z.path.edges vertices
      let mcells := OracleMask.cells z.demand.sourceWord z.demand.targetWord z.path.edges vertices
      let slots := (vertices.zip caps).zipWith (fun (v,q) enabled =>
        (⟨enabled,v,0,q⟩ : CapacityBottleneck.Slot)) mask
      let cnext := pnext+mcells+3
      let selected := RetainedArgminProgram.select (CapacityBottleneck.items cnext slots)
      (OracleMask.steps z.demand.sourceWord z.demand.targetWord z.path.edges vertices+
        CapacityBottleneck.selectedSteps cnext slots+19+(if selected.isNone then 8 else 5),
       mcells+CapacityBottleneck.selectedCells cnext slots+4)
  let count := dsteps+psteps+9
  let cells := 1+dcells+pcells
  let actual := execute GraphOracleMachine.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let decoded := do
    let some (.pair mask word) := heap[value actual.state.registers.d]? | none
    return (←readBits heap (heap.length+1) mask,value (←readBits heap (heap.length+1) word))
  unless actual.halted && actual.instructions==count && decoded==some (expectedMask,expectedVertex) &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations ≤ completeBound 2120 (initial.heap.length+1) (initial.heap.length+1) count do
    throw (IO.userError ("FAILED full oracle "++name++" steps="++toString actual.instructions++
      " expected="++toString count++" cells="++toString (actual.state.heap.length-initial.heap.length)++
      " expected="++toString cells))
  IO.println ("PASS actual full oracle "++name++" steps="++toString count)
  (←IO.getStdout).flush

def main (args : List String) : IO Unit := do
  if args==["small"] then
    check "no-demands" [[]] [[false]] [] [true] 0
    check "singleton-self" [[]] [[false]] [([],[])] [false] 0
    check "unreachable-default" [[],[true]] [[false,false],[false,false]] [([],[true])] [true,false] 0
  else if args==["chain"] then
    check "unreachable-then-chain" [[],[true],[false,true]]
      [[false,true,false],[false,false,true],[false,false,false]] [([false,true],[]),([],[false,true])]
      [false,true,false] 1
  else if args==["padded"] then
    check "padded-labels" [[false,false],[true,false],[false,true,false]]
      [[false,true,false],[false,false,true],[false,false,false]] [([false,false],[false,true,false])]
      [false,true,false] 1
  else if args==["cycle"] then
    check "zero-cycle-tie" [[],[true],[false,true]]
      [[false,true,false],[true,false,true],[false,false,false]] [([],[false,true]),([true],[false,true])]
      [false,true,false] 1 true

end DirectedFlowCutGap.GraphOracleSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.GraphOracleSmoke.main args
