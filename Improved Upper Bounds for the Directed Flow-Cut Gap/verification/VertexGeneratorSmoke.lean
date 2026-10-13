import DirectedFlowCutGap.ActualEnumeratedPacking
import DirectedFlowCutGap.ActualRowVertices
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.VertexGeneratorSmoke
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

def readVertices (heap : NaturalHeap) : ℕ → ℕ → Option (List Bits)
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      return (←readBits heap (heap.length+1) head)::(←readVertices heap fuel tail)
    | _ => none

def check (name : String) (xs : List Fraction) : IO Unit := do
  let caps := prepare xs ⟨[],[],[],0⟩
  let initial : BitState 44 := ⟨caps.heap,caps.next,⟨caps.root,[],[],[]⟩,[],40,[true,false]⟩
  let actual := execute RowVertices.program 20000 initial
  let heap := (eraseState actual.state).heap
  let wanted := (List.range xs.length).map Nat.bits
  let bound := RowVertices.instructionBound xs.length
  unless actual.halted && readVertices heap (heap.length+1) (value actual.state.registers.d)==some wanted &&
      actual.instructions≤bound && actual.operations≤completeBound 44 (initial.heap.length+1) (initial.heap.length+1) bound &&
      actual.state.pc==43 && actual.state.stack.isEmpty && actual.state.source==initial.source && actual.events.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap && value actual.state.next==actual.state.heap.length do
    throw (IO.userError ("FAILED vertex generator "++name))
  IO.println ("PASS actual vertex generator "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "empty" []
  check "one-zero" [zero]
  check "one-padded" [padded]
  check "two-mixed" [one,padded]
  check "three" (List.replicate 3 zero)
  check "four" (List.replicate 4 one)
  check "eight" (List.replicate 8 padded)
  check "sixteen" (List.replicate 16 zero)
end DirectedFlowCutGap.VertexGeneratorSmoke

def main := DirectedFlowCutGap.VertexGeneratorSmoke.main
