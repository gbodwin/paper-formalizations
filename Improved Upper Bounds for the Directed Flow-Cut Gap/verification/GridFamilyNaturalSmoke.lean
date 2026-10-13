import DirectedFlowCutGap.ActualGridFamily
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.GridFamilyNaturalSmoke
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
    (exponent fuel : Bits) (chosen : Option (Fin n)) : IO Unit := do
  IO.println ("BEGIN natural-reference grid family "++name)
  (←IO.getStdout).flush
  let label : Fin n → Bits := RowVertices.vertexLabel
  let caps := prepare capacity.toList PackedWordPairTable.seed
  let exp := PackedWordPairTable.word exponent caps
  let remaining := PackedWordPairTable.word fuel exp
  let matrix := wordList (GraphRelaxationRefinement.matrix adjacency) remaining
  let (demandInput,_) := demands (ds.map fun (u,v) => (label u,label v)) matrix
  let tail := PackedWordPairTable.allocate (.pair matrix.root demandInput.root) demandInput
  let context := PackedWordPairTable.allocate (.pair caps.root tail.root) tail
  let initial : NaturalState 10180 := ⟨(eraseState (⟨context.heap,context.next,⟨context.root,exp.root,remaining.root,[]⟩,[],10178,[true,false,true]⟩ : BitState 10180)).heap,
    value context.next,⟨value context.root,value exp.root,value remaining.root,0⟩,[],10178,[true,false,true]⟩
  let actual := execute GridFamily.program 500000 initial
  IO.println ("EXECUTED "++name++" steps="++toString actual.instructions)
  (←IO.getStdout).flush
  let heap := actual.state.heap
  let decoded := readFamily heap (heap.length+1) (actual.state.registers.d)
  let wanted := match chosen with
    | none => List.replicate (value fuel) none
    | some j => ((BinaryFractionalGuesses.guessesFrom adjacency ds capacity j
        (BinaryFractionalCore.dimension capacity).1 exponent fuel).results).map (fun r => some (raw r.state))
  let bound := GridFamily.instructionBound ds.length capacity.toList exponent fuel+1
  unless actual.halted && decoded==some wanted && actual.instructions ≤ bound &&
      (BinaryFractionalDispatch.minimumPositive capacity).1==chosen &&
      actual.state.pc==10179 && actual.state.registers.a==initial.registers.a &&
      actual.state.registers.b==initial.registers.b && actual.state.registers.c==initial.registers.c &&
      readRow heap (heap.length+1) (value caps.root)==some (fields capacity.toList) &&
      readBits heap (heap.length+1) (value exp.root)==some exponent &&
      readBits heap (heap.length+1) (value remaining.root)==some fuel &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.next==actual.state.heap.length && actual.events.isEmpty &&
      actual.state.source==initial.source && actual.state.stack.isEmpty do
    throw (IO.userError ("FAILED grid family "++name++" pc="++toString actual.state.pc.val++
      " steps="++toString actual.instructions++" decoded="++reprStr decoded++" wanted="++reprStr wanted))
  IO.println ("PASS natural-reference grid family "++name++" steps="++toString actual.instructions)

def chain (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n :=
  Vector.ofFn fun i => Vector.ofFn fun j => decide (i.val+1=j.val)
def emptyGraph (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n := Vector.replicate n (Vector.replicate n false)
def row (xs : List Fraction) : BinaryFractionalRows.Row xs.length := ⟨xs.toArray,by simp⟩
def main (args : List String) : IO Unit := do
  match args.headD "empty-stop" with
  | "empty-stop" => check "empty-stop" (emptyGraph 0) (row []) [] [] [] none
  | "positive-stop" => check "positive-stop" (emptyGraph 1) (row [one]) [] [] [] (some 0)
  | "padded-stop" => check "padded-stop" (chain 2) (row [one,one]) [(0,1)] [true,false] [false,false,false] (some 0)
  | "empty-one" => check "empty-one" (emptyGraph 0) (row []) [] [] [true] none
  | "empty-three" => check "empty-three" (emptyGraph 0) (row []) [] [true] [true,true] none
  | "zero-one" => check "zero-one" (emptyGraph 1) (row [zero]) [] [] [true] none
  | "zero-two" => check "zero-two" (emptyGraph 1) (row [zero]) [] [] [false,true] none
  | "zeros-three" => check "zeros-three" (chain 2) (row [frac 0 2,zero]) [(0,1)] [] [true,true] none
  | "padded-count" => check "padded-count" (emptyGraph 1) (row [zero]) [] [false,false] [false,true,false,false] none
  | "carry" => check "carry" (emptyGraph 0) (row []) [] [true,true,true] [false,true] none
  | "one" => check "one" (emptyGraph 1) (row [one]) [] [] [true] (some 0)
  | "diagonal" => check "diagonal" (emptyGraph 1) (row [one]) [(0,0)] [] [true] (some 0)
  | "two-guesses" => check "two-guesses" (emptyGraph 1) (row [one]) [] [] [false,true] (some 0)
  | "padded-guesses" => check "padded-guesses" (emptyGraph 1) (row [padded]) [] [false,false] [false,true,false] (some 0)
  | "direct" => check "direct" (chain 2) (row [one,one]) [(0,1)] [] [true] (some 0)
  | _ => throw (IO.userError "unknown fixture group")
end DirectedFlowCutGap.GridFamilyNaturalSmoke

def main := DirectedFlowCutGap.GridFamilyNaturalSmoke.main
