import DirectedFlowCutGap.ActualOracleMask
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.OracleMaskSmoke
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

def check (name : String) (vs : List Bits) (sw target : Bits) (es : List (Bits×Bits)) : IO Unit := do
  let er := edges es ⟨[],[],[],0⟩
  let sr := PackedWordPairTable.word sw er
  let tr := PackedWordPairTable.word target sr
  let d := PackedWordPairTable.allocate (.pair sr.root tr.root) tr
  let c := PackedWordPairTable.allocate (.pair d.root er.root) d
  let v := wordList vs c
  let initial : BitState 160 := ⟨v.heap,v.next,⟨v.root,c.root,[],[]⟩,[],150,[true,false,true]⟩
  let count := OracleMask.steps sw target es vs+1
  let cells := OracleMask.cells sw target es vs
  let actual := execute OracleMask.program (count+1) initial
  let heap := (eraseState actual.state).heap
  unless actual.halted && actual.instructions==count &&
      readBits heap (heap.length+1) (value actual.state.registers.d)==some (OracleMask.mask sw target es vs) &&
      actual.events.isEmpty && actual.state.source==initial.source && actual.state.stack.isEmpty &&
      actual.state.heap.take initial.heap.length==initial.heap &&
      actual.state.heap.length==initial.heap.length+cells && value actual.state.next==actual.state.heap.length &&
      actual.operations ≤ completeBound 160 (initial.heap.length+1) (initial.heap.length+1) count do
    throw (IO.userError ("FAILED actual mask "++name++" steps="++toString actual.instructions++" expected="++toString count))
  IO.println ("PASS actual mask "++name++" steps="++toString count++" cells="++toString cells)

def main : IO Unit := do
  check "empty-enumeration" [] [] [true] []
  check "empty-path" [[],[true],[false,true]] [] [false,true] []
  check "internal-chain" [[],[true],[false,true]] [] [false,true] [([],[true]),([true],[false,true])]
  check "padded-equality" [[false,false],[true,false],[false,true,false]] [] [false,true]
    [([false],[true,false,false]),([true],[false,true,false,false])]
  check "target-tail-excluded" [[],[true],[false,true]] [] [false,true]
    [([false,true],[true]),([true],[])]
  check "duplicate-tails" [[],[true],[false,true],[true,true]] [] [true,true]
    [([true],[true]),([true],[false,true]),([false,true],[true,true])]

end DirectedFlowCutGap.OracleMaskSmoke

def main : IO Unit := DirectedFlowCutGap.OracleMaskSmoke.main
