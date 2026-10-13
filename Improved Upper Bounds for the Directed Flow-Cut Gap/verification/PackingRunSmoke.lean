import DirectedFlowCutGap.PackingRunProgram
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PackingRunSmoke
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

def check {n : ℕ} (name : String) (hn : 0<n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : BinaryFractionalRows.Row n) (delta : Fraction)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (fuel : Bits) (pad : Bool := false) : IO Unit := do
  IO.println ("BEGIN actual packing run "++name)
  (←IO.getStdout).flush
  let label : Fin n → Bits := fun i => i.val.bits++(if pad then [false,false] else [])
  let vertices := List.ofFn label
  let rows := GraphRelaxationRefinement.matrix adjacency
  let caps := prepare capacity.toList ⟨[],[],[],0⟩
  let scalarInput := scalar delta caps
  let matrix := wordList rows scalarInput
  let enumeration := wordList vertices matrix
  let post := PackedWordPairTable.allocate (.pair enumeration.root caps.root) enumeration
  let detail := PackedWordPairTable.allocate (.pair matrix.root post.root) post
  let metadata := PackedWordPairTable.allocate (.pair enumeration.root detail.root) detail
  let (demandInput,_) := demands (ds.map fun (u,v) => (label u,label v)) metadata
  let context := PackedWordPairTable.allocate (.pair demandInput.root metadata.root) demandInput
  let fuelWord := PackedWordPairTable.word fuel context
  let fullContext := PackedWordPairTable.allocate (.pair context.root fuelWord.root) fuelWord
  let initial : BitState 7960 := ⟨fullContext.heap,fullContext.next,⟨caps.root,scalarInput.root,fullContext.root,[]⟩,[],7940,[true,false,true]⟩
  let expected := (BinaryFractionalCore.run capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel).state
  IO.println ("EXPECTED ready "++name)
  (←IO.getStdout).flush
  let actual := execute PackingRun.program 150000 initial
  IO.println ("EXECUTED ready "++name++" steps="++toString actual.instructions)
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
  let wanted := (fields expected.weights.toList,fields expected.best.toList,
    (expected.bestCost.num,expected.bestCost.den),(expected.total.num,expected.total.den),fields expected.loads.toList,
    expected.events.map fun e => (e.choice.mask.toList,label e.choice.bottleneck,(e.amount.num,e.amount.den)))
  unless actual.halted && decoded==some wanted &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      value actual.state.next==actual.state.heap.length && actual.events.isEmpty &&
      actual.state.source==initial.source && actual.state.stack.isEmpty do
    throw (IO.userError ("FAILED adaptive state "++name++" pc="++toString actual.state.pc.val++
      " steps="++toString actual.instructions++" decoded="++reprStr decoded++" wanted="++reprStr wanted))
  IO.println ("PASS actual packing run "++name++" steps="++toString actual.instructions)

def initialState {n : ℕ} (weight best cost : Fraction) : BinaryFractionalCore.State n :=
  ⟨Vector.replicate n weight,Vector.replicate n best,cost,zero,Vector.replicate n zero,[]⟩

def chain (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n :=
  Vector.ofFn fun i => Vector.ofFn fun j => decide (i.val+1=j.val)
def emptyGraph (n : ℕ) : BinaryFractionalWalkOracle.Adjacency n := Vector.replicate n (Vector.replicate n false)

def main (args : List String) : IO Unit := do
  let group := args.headD "all"
  if group=="all" || group=="zero" then
    check "initialize-empty-fuel" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 one) (frac 1 3) [] []
    check "initialize-padded-zero" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 padded) padded [] [false,false] true
  if group=="all" || group=="active" then
    check "initialized-one-step" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 one) (frac 1 3) [] [true]
    check "initialized-two-zero-steps" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 one) zero [] [false,true] true
  if group=="all" || group=="graph" then
    check "unreachable-initialized" (by decide : 0<2) (emptyGraph 2) (Vector.replicate 2 one) zero [(0,1)] [true]
  if group=="all" || group=="internal" then
    check "internal-zero-initialized" (by decide : 0<3) (chain 3) (Vector.replicate 3 one) zero [(0,2)] [true]
  if group=="all" || group=="stop" then
    check "positive-delta-empty-demand" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 one) one [] [true]
    check "zero-capacity-padded-fuel" (by decide : 0<1) (emptyGraph 1) (Vector.replicate 1 zero) padded [] [true,false] true
end DirectedFlowCutGap.PackingRunSmoke

def main := DirectedFlowCutGap.PackingRunSmoke.main
