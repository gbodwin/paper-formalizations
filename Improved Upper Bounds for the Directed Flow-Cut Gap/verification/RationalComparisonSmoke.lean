import DirectedFlowCutGap.InputRationalComparisonProgram
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.RationalComparisonSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  halted : Bool

def execute {C : ℕ} (p : Program C) : ℕ → BitState C → Trace C
  | 0,s => ⟨s,[],0,false⟩
  | fuel+1,s =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,[],a.operations,true⟩
      | some r =>
          let t := execute p fuel r.state
          ⟨t.state,r.events++t.events,a.operations+t.operations,t.halted⟩

def word (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,root =>
      match heap[root]? with
      | some .nil => some []
      | some (.pair head tail) =>
          match heap[head]?,word heap fuel tail with
          | some (.flag b),some bs => some (b::bs)
          | _,_ => none
      | _ => none

def table (heap : NaturalHeap) (wordFuel : ℕ) : ℕ → ℕ → Option (List (Bits × Bits))
  | 0,_ => none
  | fuel+1,root =>
      match heap[root]? with
      | some .nil => some []
      | some (.pair item tail) =>
          match heap[item]?,table heap wordFuel fuel tail with
          | some (.pair a b),some rows =>
              match word heap wordFuel a,word heap wordFuel b with
              | some x,some y => some ((x,y)::rows)
              | _,_ => none
          | _,_ => none
      | _ => none

def binaryCheck (name : String) (xs ys : Bits) : IO Unit := do
  let l := PackedWordPairTable.word xs PackedWordPairTable.empty
  let r := PackedWordPairTable.word ys l
  let initial : BitState 48 := ⟨r.heap,r.next,⟨l.root,r.root,[],[]⟩,[],30,[true,false,true]⟩
  let t := execute BinaryComparisonProgram.program (BinaryComparisonProgram.steps xs ys+4) initial
  let heap := (eraseState t.state).heap
  unless t.halted && t.state.pc==46 && t.state.stack.isEmpty && t.events.isEmpty &&
      t.state.source==initial.source &&
      heap[value t.state.registers.d]?==some (.flag (decide (value xs ≤ value ys))) &&
      word heap (xs.length+1) (value l.root)==some xs &&
      word heap (ys.length+1) (value r.root)==some ys &&
      t.state.heap.take initial.heap.length==initial.heap &&
      t.state.heap.length==initial.heap.length+BinaryComparisonProgram.cells xs ys+1 &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ completeBound 48 (initial.heap.length+1) (initial.heap.length+1)
        (BinaryComparisonProgram.steps xs ys+3) do
    throw (IO.userError ("FAILED actual binary comparison: "++name))
  IO.println ("PASS actual binary comparison "++name)

def sourceCheck (name : String) (xn xd yn yd suffix : Bits) : IO Unit := do
  let rows := [(xn,xd),(yn,yd)]
  let source := SourceRowTableProgram.encode rows++suffix
  let start := InputRationalComparisonProgram.initial source
  let readSteps := SourceRowAcceptanceProgram.instructions rows
  let pre := execute InputRationalComparisonProgram.program readSteps start
  let root := value pre.state.registers.a
  if hx : 0 < value xd then
    if hy : 0 < value yd then
      let x : BinaryRational.Fraction := ⟨xn,xd,hx⟩
      let y : BinaryRational.Fraction := ⟨yn,yd,hy⟩
      let t := execute InputRationalComparisonProgram.program (InputRationalComparisonProgram.instructions x y+1) start
      let heap := (eraseState t.state).heap
      unless !pre.halted && pre.state.pc==216 && t.halted && t.state.pc==157 &&
          t.state.stack.isEmpty && t.state.source==suffix &&
          t.events==(SourceRowTableProgram.encode rows).map Event.request &&
          heap[value t.state.registers.d]?==some (.flag (decide (value xn*value yd ≤ value yn*value xd))) &&
          table heap (SourceRowTableProgram.bits rows+2) 3 root==some rows &&
          t.state.heap.take pre.state.heap.length==pre.state.heap &&
          t.state.heap.length==pre.state.heap.length+RationalComparisonProgram.cells x y &&
          value t.state.next==t.state.heap.length &&
          t.operations ≤ 1000000000000*(RationalComparisonProgram.inputSize x y)^6 do
        throw (IO.userError ("FAILED accepted rational comparison: "++name))
      IO.println ("PASS accepted rational comparison "++name)
    else
      reject name rows suffix pre
  else
    reject name rows suffix pre
where
  reject (name : String) (rows : List (Bits × Bits)) (suffix : Bits) (pre : Trace 221) : IO Unit := do
    let t := execute InputRationalComparisonProgram.program 1 pre.state
    let heap := (eraseState t.state).heap
    unless !pre.halted && t.halted && t.state.pc==217 && t.state.stack.isEmpty &&
        t.state.source==suffix && pre.events==(SourceRowTableProgram.encode rows).map Event.request &&
        t.events.isEmpty && t.state.heap==pre.state.heap &&
        heap[value t.state.registers.d]?==some (.flag true) &&
        table heap (SourceRowTableProgram.bits rows+2) 3 (value t.state.registers.a)==some rows &&
        t.state.heap.length==SourceRowTableProgram.cells rows+(RowTableValidationProgram.flags rows).length &&
        pre.operations+t.operations ≤ completeBound 221 1 0 (SourceRowAcceptanceProgram.instructions rows) do
      throw (IO.userError ("FAILED rejected rational comparison: "++name))
    IO.println ("PASS rejected rational comparison "++name)
end DirectedFlowCutGap.RationalComparisonSmoke
open DirectedFlowCutGap.RationalComparisonSmoke in
def main : IO Unit := do
  binaryCheck "empty" [] []
  binaryCheck "empty-padded-zero" [] [false,false,false]
  binaryCheck "padded-zero-empty" [false,false] []
  binaryCheck "empty-positive" [] [false,true,false]
  binaryCheck "positive-empty" [true,false,false] []
  for x in [false,true] do
    for y in [false,true] do
      binaryCheck (s!"one-bit-{x}-{y}") [x] [y]
  binaryCheck "higher-dominates-low" [true,false,false] [false,true]
  binaryCheck "reverse-higher-dominance" [false,false,true] [true,true]
  binaryCheck "padded-equal" [true,false,true,false,false] [true,false,true]
  sourceCheck "zero fractions" [] [true] [false,false] [false,true] [true,false]
  sourceCheck "equal different fields" [true] [false,true] [false,true] [false,false,true] [false,true]
  sourceCheck "less" [true] [true,true] [true] [false,true] []
  sourceCheck "greater" [false,true] [true,true] [true] [false,true] [true,true]
  sourceCheck "padded equality" [true,false,false] [false,true,false] [false,true,false] [false,false,true,false] [false]
  sourceCheck "unequal field widths" [true,true,true] [true] [true,false,true] [true,true] [false,true]
  sourceCheck "small positive versus zero" [true] [false,false,true] [] [true] []
  sourceCheck "zero versus small positive" [] [true,false] [true] [true,true,true] [true]
  sourceCheck "empty first denominator" [true] [] [true] [true] [true,false]
  sourceCheck "padded second zero" [true] [true] [true] [false,false] [false]
  sourceCheck "both zero denominators" [] [false] [] [] []
  IO.println "PASS all23 actual comparison fixtures"
