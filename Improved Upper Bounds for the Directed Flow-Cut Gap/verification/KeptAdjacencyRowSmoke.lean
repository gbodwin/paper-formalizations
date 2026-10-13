import DirectedFlowCutGap.ActualKeptAdjacencyRow
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.KeptAdjacencyRowSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
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

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none


def check (name : String) (a k : Bits) (keep : Bool) (expected : Bits) : IO Unit := do
  let ar := PackedWordPairTable.word a PackedWordPairTable.seed
  let kr := PackedWordPairTable.word k ar
  let flag := PackedWordPairTable.allocate (.flag keep) kr
  let ctx := PackedWordPairTable.allocate (.pair flag.root kr.root) flag
  let source := [true,false,true]
  let initial : BitState 36 := ⟨ctx.heap,ctx.next,⟨ar.root,ctx.root,ar.root,ctx.root⟩,[],34,source⟩
  let actual := execute KeptAdjacencyRow.program (KeptAdjacencyRow.steps keep a k+2) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let bound := 24*a.length+4
  unless actual.halted && readBits heap (heap.length+1) regs.d==some expected &&
      readBits heap (heap.length+1) regs.a==some a && regs.b==value ctx.root &&
      readBits heap (heap.length+1) (value kr.root)==some k &&
      heap.take ctx.heap.length==(eraseState initial).heap &&
      actual.instructions==KeptAdjacencyRow.steps keep a k+1 && actual.instructions≤bound &&
      actual.operations≤completeBound 36 (ctx.heap.length+1) (ctx.heap.length+1) bound &&
      actual.state.pc==35 && actual.state.stack.isEmpty && actual.state.source==source &&
      actual.events.isEmpty && value actual.state.next==heap.length &&
      heap.length==ctx.heap.length+5*a.length+1 do
    throw (IO.userError ("FAIL actual kept adjacency row "++name))
  IO.println ("PASS actual kept adjacency row "++name++" instructions="++toString actual.instructions)

def main : IO Unit := do
  check "fff" [false] [false] false [false]
  check "fft" [false] [true] false [false]
  check "ftf" [false] [false] true [false]
  check "ftt" [false] [true] true [false]
  check "tff" [true] [false] false [false]
  check "tft" [true] [true] false [false]
  check "ttf" [true] [false] true [false]
  check "ttt" [true] [true] true [true]
  check "empty" [] [] true []
  check "mixed-order" [true,false,true,false] [false,true,true,false] true [false,false,true,false]
  check "removed-row" [true,true,false,true] [true,true,true,false] false [false,false,false,false]
  check "all-kept" [true,false,true] [true,true,true] true [true,false,true]
end DirectedFlowCutGap.KeptAdjacencyRowSmoke

def main := DirectedFlowCutGap.KeptAdjacencyRowSmoke.main
