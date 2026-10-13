import DirectedFlowCutGap.ActualGridFamilyInput
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.GridFamilyInputNaturalSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead BinaryRational
structure Trace (C : ℕ) where
  state : NaturalState C
  instructions : ℕ
  halted : Bool
  events : List Event

def execute {C : ℕ} (p : Program C) (fuel : ℕ) (s : NaturalState C) : Trace C :=
  go fuel s 0 []
where
  go : ℕ → NaturalState C → ℕ → List Event → Trace C
  | 0,s,k,events => ⟨s,k,false,events.reverse⟩
  | fuel+1,s,k,events => match tickNatural p s with
    | none => ⟨s,k,true,events.reverse⟩
    | some r => go fuel r.state (k+1) (r.events.reverse++events)

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

def scalar (x : Fraction) (s : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let num := PackedWordPairTable.word x.num s
  let den := PackedWordPairTable.word x.den num
  PackedWordPairTable.allocate (.pair num.root den.root) den

def readEvents (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits × Bits × (Bits × Bits)))
  | 0,_ => none
  | fuel+1,p => do
    match heap[p]? with
    | some .nil => return []
    | some (.pair event tail) =>
      let some (.pair choice amt) := heap[event]? | none
      let some (.pair mask idx) := heap[choice]? | none
      let entry := (←readBits heap (heap.length+1) mask,←readBits heap (heap.length+1) idx,←readFraction heap amt)
      return entry::(←readEvents heap fuel tail)
    | _ => none

abbrev RawState := List (Bits×Bits) × List (Bits×Bits) × (Bits×Bits) × (Bits×Bits) ×
  List (Bits×Bits) × List (Bits×Bits×(Bits×Bits))

def readState (heap : NaturalHeap) (root : ℕ) : Option RawState := do
  let some (.pair yr k1) := heap[root]? | none
  let some (.pair wr k2) := heap[k1]? | none
  let some (.pair cr k3) := heap[k2]? | none
  let some (.pair zr k4) := heap[k3]? | none
  let some (.pair lr er) := heap[k4]? | none
  let es ← readEvents heap (heap.length+1) er
  return (←readRow heap (heap.length+1) yr,←readRow heap (heap.length+1) wr,
    ←readFraction heap cr,←readFraction heap zr,←readRow heap (heap.length+1) lr,es)

def readFamily (heap : NaturalHeap) : ℕ → ℕ → Option (List (Option RawState))
  | 0,_ => none
  | fuel+1,root => match heap[root]? with
    | some .nil => some []
    | some (.pair head tail) => do
      let entry ← if heap[head]?==some .nil then some none else (readState heap head).map some
      return entry::(←readFamily heap fuel tail)
    | _ => none

def raw {n : ℕ} (s : BinaryFractionalCore.State n) : RawState :=
  (fields s.weights.toList,fields s.best.toList,(s.bestCost.num,s.bestCost.den),
    (s.total.num,s.total.den),fields s.loads.toList,
    s.events.map fun e => (e.choice.mask.toList,RowVertices.vertexLabel e.choice.bottleneck,(e.amount.num,e.amount.den)))

def check {n : ℕ} (name : String) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (chosen : Option (Fin n)) : IO Unit := do
  IO.println ("BEGIN natural-reference original-input family "++name)
  (←IO.getStdout).flush
  let label : Fin n → Bits := RowVertices.vertexLabel
  let caps := prepare capacity.toList PackedWordPairTable.seed
  let matrix := wordList (GraphRelaxationRefinement.matrix adjacency) caps
  let (demandInput,_) := demands (ds.map fun (u,v) => (label u,label v)) matrix
  let initial : BitState 10760 := ⟨demandInput.heap,demandInput.next,
    ⟨caps.root,matrix.root,demandInput.root,[]⟩,[],10758,[true,false,true]⟩
  let actual := execute GridFamilyInput.program 500000 (eraseState initial)
  IO.println ("EXECUTED "++name++" steps="++toString actual.instructions)
  (←IO.getStdout).flush
  let heap := actual.state.heap
  let decoded := readFamily heap (heap.length+1) actual.state.registers.d
  let originalFuel := (BinaryFractionalGuesses.gridFuel (BinaryFractionalCore.dimension capacity).1
    (BinaryFractionalGuesses.inputWidth capacity).1).1
  let wanted := match chosen with
    | none => List.replicate (value originalFuel) none
    | some j => ((BinaryFractionalGuesses.guesses adjacency ds capacity j
        (BinaryFractionalGuesses.inputWidth capacity).1).results).map (fun r => some (raw r.state))
  let bound := GridFamilyInput.inputSteps ds.length capacity.toList
  unless actual.halted && decoded==some wanted && actual.instructions ≤ bound &&
      (BinaryFractionalDispatch.minimumPositive capacity).1==chosen &&
      actual.state.pc==10759 && actual.state.registers.a==value initial.registers.a &&
      actual.state.registers.b==value initial.registers.b && actual.state.registers.c==value initial.registers.c &&
      readRow heap (heap.length+1) (value caps.root)==some (fields capacity.toList) &&
      actual.state.heap.take initial.heap.length==(eraseState initial).heap &&
      actual.state.next==actual.state.heap.length && actual.events.isEmpty &&
      actual.state.source==initial.source && actual.state.stack.isEmpty do
    throw (IO.userError ("FAILED original-input family "++name++" pc="++toString actual.state.pc.val++
      " steps="++toString actual.instructions++" decoded="++reprStr decoded++" wanted="++reprStr wanted))
  IO.println ("PASS natural-reference original-input family "++name++" steps="++toString actual.instructions)

def chain (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n :=
  Vector.ofFn fun i => Vector.ofFn fun j => decide (i.val+1=j.val)
def emptyGraph (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n := Vector.replicate n (Vector.replicate n false)
def row (xs : List Fraction) : BinaryFractionalRows.Row xs.length := ⟨xs.toArray,by simp⟩
def paddedZero : Fraction := ⟨[false,false,false],[true,false,false],by decide⟩
def main (args : List String) : IO Unit := do
  match args.headD "empty" with
  | "empty" => check "empty" (emptyGraph 0) (row []) [] none
  | "zero" => check "zero" (emptyGraph 1) (row [zero]) [] none
  | "zero-loop" => check "zero-loop" (emptyGraph 1) (row [zero]) [(0,0)] none
  | "zero-denominator2" => check "zero-denominator2" (emptyGraph 1) (row [frac 0 1]) [] none
  | "zero-denominator3" => check "zero-denominator3" (emptyGraph 1) (row [frac 0 2]) [] none
  | "padded-zero" => check "padded-zero" (emptyGraph 1) (row [paddedZero]) [] none
  | "two-zero" => check "two-zero" (emptyGraph 2) (row [zero,zero]) [] none
  | "two-direct" => check "two-direct" (chain 2) (row [zero,zero]) [(0,1)] none
  | "two-reverse" => check "two-reverse" (chain 2) (row [zero,zero]) [(1,0)] none
  | "two-padded" => check "two-padded" (chain 2) (row [paddedZero,frac 0 2]) [(0,1),(0,0)] none
  | "three-zero" => check "three-zero" (chain 3) (row [zero,zero,zero]) [(0,2)] none
  | "three-padded" => check "three-padded" (chain 3) (row [paddedZero,frac 0 1,zero]) [(2,0),(1,1)] none
  | "positive" => check "positive" (emptyGraph 1) (row [one]) [] (some 0)
  | "positive-loop" => check "positive-loop" (emptyGraph 1) (row [one]) [(0,0)] (some 0)
  | "positive-padded" => check "positive-padded" (emptyGraph 1) (row [padded]) [] (some 0)
  | _ => throw (IO.userError "unknown fixture group")
end DirectedFlowCutGap.GridFamilyInputNaturalSmoke

def main := DirectedFlowCutGap.GridFamilyInputNaturalSmoke.main
