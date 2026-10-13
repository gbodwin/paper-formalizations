import DirectedFlowCutGap.ActualMinimumGuess
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.MinimumGuessSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead BinaryRational
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

def executeDiagnostic {C : ℕ} (p : Program C) : ℕ → BitState C → IO (Trace C)
  | 0,s => return ⟨s,[],0,0,false⟩
  | chunks+1,s => do
      let r := execute p 1000 s
      IO.println ("CHUNK pc="++toString r.state.pc.val++" heap="++toString r.state.heap.length++
        " steps="++toString r.instructions++" halted="++toString r.halted)
      (←IO.getStdout).flush
      if r.halted then return r
      let t ← executeDiagnostic p chunks r.state
      return ⟨t.state,r.events++t.events,r.operations+t.operations,r.instructions+t.instructions,t.halted⟩

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

def check {n : ℕ} (name : String) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (exponent : Bits) (chosen : Option (Fin n)) : IO Unit := do
  IO.println ("BEGIN actual minimum guess "++name)
  (←IO.getStdout).flush
  let label : Fin n → Bits := RowVertices.vertexLabel
  let rows := GraphRelaxationRefinement.matrix adjacency
  let caps := prepare capacity.toList PackedWordPairTable.seed
  let exp := PackedWordPairTable.word exponent caps
  let matrix := wordList rows exp
  let (demandInput,_) := demands (ds.map fun (u,v) => (label u,label v)) matrix
  let initial : BitState 10000 := ⟨demandInput.heap,demandInput.next,
    ⟨caps.root,exp.root,matrix.root,demandInput.root⟩,[],9998,[true,false,true]⟩
  let actual := execute MinimumGuess.program 200000 initial
  IO.println ("EXECUTED "++name++" steps="++toString actual.instructions)
  (←IO.getStdout).flush
  let heap := (eraseState actual.state).heap
  let decoded := do
    let some (.pair yr k1) := heap[value actual.state.registers.d]? | none
    let some (.pair wr k2) := heap[k1]? | none
    let some (.pair cr k3) := heap[k2]? | none
    let some (.pair zr k4) := heap[k3]? | none
    let some (.pair lr er) := heap[k4]? | none
    let es ← readEvents heap (heap.length+1) er
    return (←readRow heap (heap.length+1) yr,←readRow heap (heap.length+1) wr,
      ←readFraction heap cr,←readFraction heap zr,←readRow heap (heap.length+1) lr,es)
  let wanted := chosen.map fun i =>
    let expected := (BinaryFractionalGuesses.guess adjacency ds capacity i
      (BinaryFractionalCore.dimension capacity).1 exponent).state
    (fields expected.weights.toList,fields expected.best.toList,
      (expected.bestCost.num,expected.bestCost.den),(expected.total.num,expected.total.den),fields expected.loads.toList,
      expected.events.map fun e => (e.choice.mask.toList,label e.choice.bottleneck,(e.amount.num,e.amount.den)))
  let correct := match chosen with
    | none => heap[value actual.state.registers.d]?==some .nil
    | some _ => decoded==wanted
  let bound := MinimumGuess.inputSteps ds.length capacity.toList exponent
  unless actual.halted && correct && actual.instructions ≤ bound &&
      (BinaryFractionalDispatch.minimumPositive capacity).1==chosen &&
      actual.operations ≤ completeBound 10000 (initial.heap.length+1) (initial.heap.length+1) bound &&
      actual.state.pc==9999 && actual.state.registers.a==initial.registers.a &&
      actual.state.registers.b==initial.registers.b && actual.state.registers.c==initial.registers.c &&
      readRow heap (heap.length+1) (value caps.root)==some (fields capacity.toList) &&
      readBits heap (heap.length+1) (value exp.root)==some exponent &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      value actual.state.next==actual.state.heap.length && actual.events.isEmpty &&
      actual.state.source==initial.source && actual.state.stack.isEmpty do
    throw (IO.userError ("FAILED minimum guess "++name++" pc="++toString actual.state.pc.val++
      " steps="++toString actual.instructions++" decoded="++reprStr decoded++" wanted="++reprStr wanted))
  IO.println ("PASS actual minimum guess "++name++" steps="++toString actual.instructions)

def chain (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n :=
  Vector.ofFn fun i => Vector.ofFn fun j => decide (i.val+1=j.val)
def emptyGraph (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n := Vector.replicate n (Vector.replicate n false)
def row (xs : List Fraction) : BinaryFractionalRows.Row xs.length := ⟨xs.toArray,by simp⟩
def main (args : List String) : IO Unit := do
  match args.headD "empty" with
  | "empty" => check "empty" (emptyGraph 0) (row []) [] [] none
  | "zero" => check "zero" (emptyGraph 1) (row [zero]) [] [] none
  | "zeros" => check "zeros" (chain 2) (row [frac 0 2,zero]) [(0,1)] [] none
  | "paddedzero" => check "paddedzero" (emptyGraph 1) (row [⟨[false,false],[true,false],by decide⟩]) [] [false,false] none
  | "one" => check "one" (emptyGraph 1) (row [one]) [] [] (some 0)
  | "half" => check "half" (emptyGraph 1) (row [frac 1 1]) [] [] (some 0)
  | "padded" => check "padded" (emptyGraph 1) (row [padded]) [] [false,false] (some 0)
  | "first" => check "first" (emptyGraph 2) (row [one,frac 2 0]) [] [] (some 0)
  | "second" => check "second" (emptyGraph 2) (row [frac 2 0,one]) [] [] (some 1)
  | "ties" => check "ties" (emptyGraph 2) (row [frac 1 1,frac 2 3]) [] [] (some 0)
  | "diagonal" => check "diagonal" (emptyGraph 1) (row [one]) [(0,0)] [] (some 0)
  | "direct" => check "direct" (chain 2) (row [one,one]) [(0,1)] [] (some 0)
  | _ => throw (IO.userError "unknown fixture group")
end DirectedFlowCutGap.MinimumGuessSmoke

def main := DirectedFlowCutGap.MinimumGuessSmoke.main
