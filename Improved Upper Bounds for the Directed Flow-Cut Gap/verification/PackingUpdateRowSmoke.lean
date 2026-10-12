import DirectedFlowCutGap.ActualPackingUpdateRow
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PackingUpdateRowSmoke
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



def scalar (x : Fraction) (s : PackedWordPairTable.Prepared) : PackedWordPairTable.Prepared :=
  let num := PackedWordPairTable.word x.num s
  let den := PackedWordPairTable.word x.den num
  PackedWordPairTable.allocate (.pair num.root den.root) den

def prepareFlags : List Bool → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | b::bs,s =>
    let tail := prepareFlags bs s
    let head := PackedWordPairTable.allocate (.flag b) tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

def check (name : String) (cs ys : List Fraction) (mask : List Bool) (amount : Fraction) : IO Unit := do
  let cap := prepare cs ⟨[],[],[],0⟩
  let weights := prepare ys cap
  let flags := prepareFlags mask weights
  let amt := scalar amount flags
  let ctx := PackedWordPairTable.allocate (.pair flags.root amt.root) amt
  let initial : BitState 520 := ⟨ctx.heap,ctx.next,⟨cap.root,weights.root,ctx.root,[]⟩,[],518,[false,true]⟩
  let count := 1+PackingUpdateRow.steps amount cs ys mask
  let expected := PackingUpdateRow.result amount cs ys mask
  let actual := execute PackingUpdateRow.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let decoded := readRow heap (heap.length+1) (value actual.state.registers.a)
  let B := width (cs++ys++[amount])
  let bound := PackingUpdateRow.instructionBound cs.length B
  unless actual.halted && actual.instructions==count && decoded==some (fields expected) &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+PackingUpdateRow.cells amount cs ys mask &&
      value actual.state.next==actual.state.heap.length && actual.events.isEmpty &&
      actual.state.source==initial.source && actual.state.stack.isEmpty && actual.state.pc==519 &&
      count≤bound && actual.operations≤completeBound 520 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED actual update row "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual update row "++name++" steps="++toString count)

def main (args : List String) : IO Unit := do
  let group := args.headD "all"
  if group=="all" || group=="a" then
    check "empty" [] [] [] one
    check "false" [one,zero] [padded,one] [false,false] one
    check "true" [one,one] [one,one] [true,true] one
    check "alternating" [one,zero,one] [one,padded,zero] [true,false,true] one
  if group=="all" || group=="b" then
    check "zero-amount" [one] [one] [true] zero
    check "zero-capacity" [zero] [one] [true] one
    check "padded" [padded] [padded] [true] padded
    check "fractional" [frac 1 1,frac 2 2] [frac 1 2,frac 3 1] [true,true] (frac 1 3)
end DirectedFlowCutGap.PackingUpdateRowSmoke

def main := DirectedFlowCutGap.PackingUpdateRowSmoke.main
