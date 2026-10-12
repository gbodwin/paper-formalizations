import DirectedFlowCutGap.ActualPackingGuard
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.PackingGuardSmoke
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



def check (name : String) (cs ys : List Fraction) : IO Unit := do
  let cap := prepare cs ⟨[],[],[],0⟩
  let weights := prepare ys cap
  let loads := prepare (List.replicate ys.length zero) weights
  let zeroNum := PackedWordPairTable.word zero.num loads
  let zeroDen := PackedWordPairTable.word zero.den zeroNum
  let zr := PackedWordPairTable.allocate (.pair zeroNum.root zeroDen.root) zeroDen
  let events := PackedWordPairTable.allocate .nil zr
  let k4 := PackedWordPairTable.allocate (.pair loads.root events.root) events
  let k3 := PackedWordPairTable.allocate (.pair zr.root k4.root) k4
  let k2 := PackedWordPairTable.allocate (.pair zr.root k3.root) k3
  let k1 := PackedWordPairTable.allocate (.pair weights.root k2.root) k2
  let stored := PackedWordPairTable.allocate (.pair weights.root k1.root) k1
  let initial : BitState 484 := ⟨stored.heap,stored.next,⟨cap.root,stored.root,events.root,[]⟩,[],470,[true,false]⟩
  let count := PackingGuard.steps cs ys
  let expected := (BinaryRational.le one (ObjectiveRow.result cs ys)).1
  let B := max (width cs) (width ys)
  let bound := PackingGuard.instructionBound cs.length B
  let actual := execute PackingGuard.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let result := match heap[value actual.state.registers.d]? with
    | some (.flag b) => some b
    | _ => none
  let againInput : BitState 484 :=
    ⟨actual.state.heap,actual.state.next,⟨cap.root,stored.root,events.root,[]⟩,[],470,initial.source⟩
  let again := execute PackingGuard.program (count+1) againInput
  let againHeap := (eraseState again.state).heap
  let againResult := match againHeap[value again.state.registers.d]? with
    | some (.flag b) => some b
    | _ => none
  unless actual.halted && actual.instructions==count && result==some expected &&
      again.halted && again.instructions==count && againResult==some expected &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+PackingGuard.cells cs ys &&
      value actual.state.next==actual.state.heap.length && actual.events.isEmpty &&
      actual.state.source==initial.source && actual.state.stack.isEmpty && actual.state.pc==480 &&
      count≤bound && actual.operations≤completeBound 484 (initial.heap.length+1) (initial.heap.length+1) bound do
    throw (IO.userError ("FAILED actual guard "++name))
  IO.println ("PASS actual guard "++name++" steps="++toString count++" stop="++toString expected)

def main : IO Unit := do
  check "empty" [] []
  check "zero" [one] [zero]
  check "below" [one] [frac 1 1]
  check "equality" [one] [one]
  check "above" [frac 2 0] [one]
  check "padded" [padded,one] [one,frac 1 1]
end DirectedFlowCutGap.PackingGuardSmoke

def main := DirectedFlowCutGap.PackingGuardSmoke.main
