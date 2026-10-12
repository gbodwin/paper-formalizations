import DirectedFlowCutGap.ActualCapacityBottleneck
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.CapacityBottleneckSmoke
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

def check (name : String) (xs : List (Bits×Fraction×Bool)) (expected : Option ℕ) : IO Unit := do
  let built := prepare xs ⟨[],[],[],0⟩
  let ctx := PackedWordPairTable.allocate (.pair built.vertices built.table) built.heap
  let initial : BitState 244 := ⟨ctx.heap,ctx.next,⟨built.maskRoot,ctx.root,[],[]⟩,[],240,[true,false,true]⟩
  let count := CapacityBottleneck.selectedSteps (value initial.next) built.slots
  let cells := CapacityBottleneck.selectedCells (value initial.next) built.slots
  let actual := execute CapacityBottleneck.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let items := CapacityBottleneck.items (value initial.next) built.slots
  let result := match heap[value actual.state.registers.d]? with
    | some (.pair _ word) => (readBits heap (heap.length+1) word).map value
    | _ => none
  let original := match RetainedArgminProgram.select items with
    | none => heap[value actual.state.registers.d]?==some .nil
    | some z => value actual.state.registers.d==z.address
  let records := items.all fun z => match heap[z.address]? with
    | some (.pair score payload) => payload==z.payload &&
        readFraction heap score==some (z.score.num,z.score.den)
    | _ => false
  unless actual.halted && actual.instructions==count && result==expected && original && records &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations ≤ completeBound 244 (initial.heap.length+1) (initial.heap.length+1) count do
    throw (IO.userError ("FAILED actual bottleneck "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual bottleneck "++name++" steps="++toString count++" candidates="++toString items.length)

def main : IO Unit := do
  check "empty-domain" [] none
  check "empty-mask" [([],frac 1 0,false),([true],frac 1 0,false)] none
  check "one-enabled" [([],frac 0 0,false),([true],frac 3 0,true)] (some 1)
  check "masked-cheaper" [([],frac 0 0,false),([true],frac 3 0,true),([false,true],frac 2 0,true)] (some 2)
  check "first-tie" [([],frac 1 1,true),([true],frac 2 3,true),([false,true],frac 1 0,true)] (some 0)
  check "padded-words" [([false,false],frac 1 0,true),([true,false,false],padded,true)] (some 1)

end DirectedFlowCutGap.CapacityBottleneckSmoke

def main : IO Unit := DirectedFlowCutGap.CapacityBottleneckSmoke.main
