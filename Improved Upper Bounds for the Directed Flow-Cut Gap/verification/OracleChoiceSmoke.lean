import DirectedFlowCutGap.OracleChoiceProgram
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.OracleChoiceSmoke
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

structure Built where
  heap : PackedWordPairTable.Prepared
  maskRoot : Bits
  vertices : Bits
  table : Bits
  slots : List CapacityBottleneck.Slot

def prepare : List (Bits×Fraction×Bool) → PackedWordPairTable.Prepared → Built
  | [],s =>
    let e := PackedWordPairTable.allocate .nil s
    ⟨e,e.root,e.root,e.root,[]⟩
  | (word,q,enabled)::xs,s =>
    let t := prepare xs s
    let w := PackedWordPairTable.word word t.heap
    let num := PackedWordPairTable.word q.num w
    let den := PackedWordPairTable.word q.den num
    let score := PackedWordPairTable.allocate (.pair num.root den.root) den
    let f := PackedWordPairTable.allocate (.flag enabled) score
    let m := PackedWordPairTable.allocate (.pair f.root t.maskRoot) f
    let v := PackedWordPairTable.allocate (.pair w.root t.vertices) m
    let row := PackedWordPairTable.allocate (.pair score.root t.table) v
    ⟨row,m.root,v.root,row.root,⟨enabled,word,value w.root,q⟩::t.slots⟩


structure DemandPath where
  sourceWord : Bits
  targetWord : Bits
  pathEdges : List (Bits×Bits)

def selectedRecord (q : DemandPath) (initial : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let nil := PackedWordPairTable.allocate .nil initial
  let sw := PackedWordPairTable.word q.sourceWord nil
  let tw := PackedWordPairTable.word q.targetWord sw
  let demand := PackedWordPairTable.allocate (.pair sw.root tw.root) tw
  let occurrence := PackedWordPairTable.allocate (.pair demand.root nil.root) demand
  let es := edges q.pathEdges occurrence
  let num := PackedWordPairTable.word [] es
  let den := PackedWordPairTable.word [true] num
  let score := PackedWordPairTable.allocate (.pair num.root den.root) den
  let walk := PackedWordPairTable.allocate (.pair es.root score.root) score
  let payload := PackedWordPairTable.allocate (.pair occurrence.root walk.root) walk
  PackedWordPairTable.allocate (.pair score.root payload.root) payload

def check (name : String) (xs : List (Bits×Fraction×Bool)) (q : Option DemandPath)
    (expectedMask : Bits) (expectedVertex : ℕ) : IO Unit := do
  let built := prepare xs ⟨[],[],[],0⟩
  let selected := match q with
    | none => PackedWordPairTable.allocate .nil built.heap
    | some d => selectedRecord d built.heap
  let ctx := PackedWordPairTable.allocate (.pair built.vertices built.table) selected
  let initial : BitState 484 := ⟨ctx.heap,ctx.next,⟨selected.root,ctx.root,[],[]⟩,[],480,[true,false,true]⟩
  let (count,cells) := match q with
    | none => (6*(xs.length-1)+15,2*(xs.length-1)+5)
    | some d =>
      let vs := xs.map Prod.fst
      let mask := OracleMask.mask d.sourceWord d.targetWord d.pathEdges vs
      let maskCells := OracleMask.cells d.sourceWord d.targetWord d.pathEdges vs
      let slots := built.slots.zipWith (fun s flag => {s with enabled:=flag}) mask
      let allocNext := value initial.next+maskCells+3
      let selected := RetainedArgminProgram.select (CapacityBottleneck.items allocNext slots)
      (OracleMask.steps d.sourceWord d.targetWord d.pathEdges vs+
        CapacityBottleneck.selectedSteps allocNext slots+19+(if selected.isNone then 8 else 5),
       maskCells+CapacityBottleneck.selectedCells allocNext slots+4)
  let actual := execute OracleChoice.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let decoded := do
    let some (.pair mask word) := heap[value actual.state.registers.d]? | none
    return (←readBits heap (heap.length+1) mask,value (←readBits heap (heap.length+1) word))
  unless actual.halted && actual.instructions==count && decoded==some (expectedMask,expectedVertex) &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations ≤ completeBound 484 (initial.heap.length+1) (initial.heap.length+1) count do
    throw (IO.userError ("FAILED actual choice "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual choice "++name++" steps="++toString count)

def main : IO Unit := do
  check "default-singleton" [([],frac 1 0,false)] none [true] 0
  check "default-multiple" [([],frac 1 0,false),([true],frac 1 0,false),([false,true],frac 1 0,false)] none [true,false,false] 0
  check "empty-internal-mask" [([],frac 2 0,false),([true],frac 1 0,false)]
    (some ⟨[],[true],[([],[true])]⟩) [false,false] 0
  check "one-internal-vertex" [([],frac 2 0,false),([true],frac 3 0,false),([false,true],frac 1 0,false)]
    (some ⟨[],[false,true],[([],[true]),([true],[false,true])]⟩) [false,true,false] 1
  check "cheapest-internal-vertex" [([],frac 0 0,false),([true],frac 3 0,false),([false,true],frac 2 0,false),([true,true],frac 0 0,false)]
    (some ⟨[],[true,true],[([],[true]),([true],[false,true]),([false,true],[true,true])]⟩) [false,true,true,false] 2
  check "first-capacity-tie" [([],frac 0 0,false),([true],frac 1 1,false),([false,true],frac 2 3,false),([true,true],frac 0 0,false)]
    (some ⟨[],[true,true],[([],[true]),([true],[false,true]),([false,true],[true,true])]⟩) [false,true,true,false] 1
  check "padded-labels" [([false,false],frac 0 0,false),([true,false],frac 1 0,false),([false,true,false],frac 2 0,false),([true,true,false],frac 0 0,false)]
    (some ⟨[],[true,true],[([],[true,false,false]),([true],[false,true]),([false,true,false],[true,true])]⟩) [false,true,true,false] 1

end DirectedFlowCutGap.OracleChoiceSmoke

def main : IO Unit := DirectedFlowCutGap.OracleChoiceSmoke.main
