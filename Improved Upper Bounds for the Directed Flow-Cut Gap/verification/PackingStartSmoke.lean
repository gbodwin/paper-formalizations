import DirectedFlowCutGap.ActualPackingStart
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PackingStartSmoke
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

def readFraction (heap : NaturalHeap) (p : ℕ) : Option (Bits×Bits) := do
  let some (.pair num den) := heap[p]? | none
  return (←readBits heap (heap.length+1) num,←readBits heap (heap.length+1) den)

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def padded : Fraction := ⟨[true,false,false],[false,true,false],by decide⟩


def prepare : List Fraction → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | x::xs,s =>
    let tail := prepare xs s
    let num := PackedWordPairTable.word x.num tail
    let den := PackedWordPairTable.word x.den num
    let q := PackedWordPairTable.allocate (.pair num.root den.root) den
    PackedWordPairTable.allocate (.pair q.root tail.root) q

def readRow (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits×Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair q rest) => do
      let value ← readFraction heap q
      return value::(←readRow heap fuel rest)
    | _ => none

def fields (xs : List Fraction) := xs.map fun x => (x.num,x.den)
def width (xs : List Fraction) := (xs.map fun x => max x.num.length x.den.length).foldl max 0


def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | w::ws,s =>
    let t := wordList ws s
    let h := PackedWordPairTable.word w t
    PackedWordPairTable.allocate (.pair h.root t.root) h


def demands : List (Bits×Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared×List DemandCollection.Demand
  | [],s => (PackedWordPairTable.allocate .nil s,[])
  | (sw,tw)::ds,s =>
    let (tail,xs) := demands ds s
    let a := PackedWordPairTable.word sw tail
    let b := PackedWordPairTable.word tw a
    let r := PackedWordPairTable.allocate (.pair a.root b.root) b
    let node := PackedWordPairTable.allocate (.pair r.root tail.root) r
    (node,⟨sw,tw,value r.root,value node.root⟩::xs)

def check {n : ℕ} (name : String) (hn : 0<n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : BinaryFractionalRows.Row n) (delta : Fraction)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (pad : Bool := false) : IO Unit := do
  IO.println ("BEGIN actual packing start "++name)
  (←IO.getStdout).flush
  let label : Fin n → Bits := fun i => i.val.bits++(if pad then [false,false] else [])
  let vertices := List.ofFn label
  let rows := GraphRelaxationRefinement.matrix adjacency
  let caps := prepare capacity.toList ⟨[],[],[],0⟩
  let num := PackedWordPairTable.word delta.num caps
  let den := PackedWordPairTable.word delta.den num
  let scalar := PackedWordPairTable.allocate (.pair num.root den.root) den
  let matrix := wordList rows scalar
  let enumeration := wordList vertices matrix
  let post := PackedWordPairTable.allocate (.pair enumeration.root caps.root) enumeration
  let detail := PackedWordPairTable.allocate (.pair matrix.root post.root) post
  let metadata := PackedWordPairTable.allocate (.pair enumeration.root detail.root) detail
  let (demandInput,xs) := demands (ds.map fun (u,v) => (label u,label v)) metadata
  let context := PackedWordPairTable.allocate (.pair demandInput.root metadata.root) demandInput
  let initial : BitState 3060 := ⟨context.heap,context.next,⟨caps.root,scalar.root,context.root,[]⟩,[],3020,[true,false,true]⟩
  let y := (BinaryFractionalRows.initial capacity delta).1
  let q := (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn y).1
  let expected := (BinaryFractionalCore.start capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).1
  let dnext := value initial.next+ScalarQuotientRow.cells true delta capacity.toList+6
  let records := DemandCollection.records vertices rows y.toList dnext xs
  let chosen := (BinaryFractionalGraphOracle.argmin DemandCollection.recordScore records).1
  let dcells := DemandCollection.selectedCells vertices rows y.toList dnext xs
  let dsteps := DemandCollection.selectedSteps vertices rows y.toList dnext xs
  let pnext := dnext+dcells
  let (psteps,pcells) := match chosen with
    | none => (6*(n-1)+15,2*(n-1)+5)
    | some z =>
      let mask := OracleMask.mask z.demand.sourceWord z.demand.targetWord z.path.edges vertices
      let mcells := OracleMask.cells z.demand.sourceWord z.demand.targetWord z.path.edges vertices
      let slots := (vertices.zip capacity.toList).zipWith (fun (v,c) enabled =>
        (⟨enabled,v,0,c⟩ : CapacityBottleneck.Slot)) mask
      let cnext := pnext+mcells+3
      let selected := RetainedArgminProgram.select (CapacityBottleneck.items cnext slots)
      (OracleMask.steps z.demand.sourceWord z.demand.targetWord z.path.edges vertices+
        CapacityBottleneck.selectedSteps cnext slots+19+(if selected.isNone then 8 else 5),
       mcells+CapacityBottleneck.selectedCells cnext slots+4)
  let count := ScalarQuotientRow.steps true delta capacity.toList+dsteps+psteps+35+
    PackingStart.finishSteps capacity y q
  let cells := ScalarQuotientRow.cells true delta capacity.toList+dcells+pcells+
    NormalizedRow.cells y.toList q.mask.toList+
    ObjectiveRow.cells capacity.toList expected.best.toList+n+20
  let actual := execute PackingStart.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let decoded := do
    let some (.pair yr k1) := heap[value actual.state.registers.d]? | none
    let some (.pair wr k2) := heap[k1]? | none
    let some (.pair cr k3) := heap[k2]? | none
    let some (.pair zr k4) := heap[k3]? | none
    let some (.pair lr er) := heap[k4]? | none
    let some .nil := heap[er]? | none
    return (←readRow heap (heap.length+1) yr,←readRow heap (heap.length+1) wr,
      ←readFraction heap cr,←readFraction heap zr,←readRow heap (heap.length+1) lr)
  let wanted := (fields expected.weights.toList,fields expected.best.toList,
    (expected.bestCost.num,expected.bestCost.den),(expected.total.num,expected.total.den),fields expected.loads.toList)
  let B := max 1 (max (width capacity.toList) (max (max delta.num.length delta.den.length)
    ((vertices.map List.length).foldl max 0)))
  let bound := PackingStart.instructionBound ds.length n B
  unless actual.halted && actual.instructions==count && decoded==some wanted && count≤bound &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.pc==3057 && actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations≤completeBound 3060 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED packing start "++name++" steps="++toString actual.instructions++
      " expected="++toString count++" cells="++toString (actual.state.heap.length-initial.heap.length)++
      " expected="++toString cells))
  IO.println ("PASS actual packing start "++name++" steps="++toString count)
  (←IO.getStdout).flush

def chain (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n :=
  Vector.ofFn fun i => Vector.ofFn fun j => decide (i.val+1=j.val)
def emptyGraph (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n := Vector.replicate n (Vector.replicate n false)
def main (args : List String) : IO Unit := do
  if args==["small"] then
    check "no-demands" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 (frac 1 0)) (frac 1 1) []
    check "singleton-self" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 (frac 1 0)) (frac 1 1) [(0,0)]
    check "zero-delta" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 (frac 2 0)) zero []
  else if args==["pair"] then
    check "unreachable-default" (by decide : 0<2) (emptyGraph 2) (Vector.replicate 2 (frac 1 0)) (frac 1 1) [(0,1)]
    check "direct-empty-mask" (by decide : 0<2) (chain 2) (Vector.replicate 2 (frac 1 0)) (frac 1 1) [(0,1)]
  else if args==["chain"] then
    check "internal-chain" (by decide : 0<3) (chain 3) (Vector.replicate 3 (frac 1 0)) (frac 1 1) [(0,2)]
  else if args==["padded"] then
    check "padded-labels" (by decide : 0<3) (chain 3) (Vector.replicate 3 (frac 1 0)) padded [(0,2)] true
  else if args==["ties"] then
    check "duplicate-demand" (by decide : 0<3) (chain 3) (Vector.replicate 3 (frac 1 0)) (frac 1 1) [(0,2),(0,2)]
end DirectedFlowCutGap.PackingStartSmoke

def main (args : List String) : IO Unit := DirectedFlowCutGap.PackingStartSmoke.main args
