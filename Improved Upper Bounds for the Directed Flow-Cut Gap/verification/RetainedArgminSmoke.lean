import DirectedFlowCutGap.RetainedGraphArgmin
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.RetainedArgminSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open RetainedArgminProgram
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

def makeInput : List BinaryRational.Fraction → PackedWordPairTable.Prepared × List Item
  | [] => (PackedWordPairTable.seed,[])
  | x::xs =>
    let t := makeInput xs
    let n := PackedWordPairTable.word x.num t.1
    let d := PackedWordPairTable.word x.den n
    let cost := PackedWordPairTable.allocate (.pair n.root d.root) d
    let payload := PackedWordPairTable.allocate .nil cost
    let record := PackedWordPairTable.allocate (.pair cost.root payload.root) payload
    let list := PackedWordPairTable.allocate (.pair record.root t.1.root) record
    (list,⟨x,value payload.root,value record.root⟩::t.2)

def check (name : String) (rows : List BinaryRational.Fraction) (expected : Option ℕ) : IO Unit := do
  let (built,items) := makeInput rows
  let initial : BitState 194 := ⟨built.heap,built.next,⟨built.root,[],[],[]⟩,[],178,[true,false,true,false]⟩
  let t := execute RetainedArgminProgram.program (steps items+1) initial
  let heap := (eraseState t.state).heap
  let selectedOK := match expected with
    | none => heap[value t.state.registers.d]?==some .nil && t.state.pc==175
    | some i => match items[i]? with
      | none => false
      | some x => value t.state.registers.d==x.address && t.state.pc==177 &&
          (match heap[x.address]? with
          | some (.pair _ p) => p==x.payload
          | _ => false)
  unless selectedOK && t.halted && t.events.isEmpty && t.state.source==initial.source &&
      t.state.stack.isEmpty && t.state.heap.take initial.heap.length==initial.heap &&
      t.state.heap.length==initial.heap.length+cells items &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ completeBound 194 (initial.heap.length+1) (initial.heap.length+1) (steps items) do
    throw (IO.userError ("FAILED actual retained argmin: "++name))
  IO.println ("PASS actual retained argmin "++name)

def frac (n d : ℕ) : BinaryRational.Fraction :=
  ⟨n.bits,(d+1).bits,by simp [value_bits]⟩

def checkGraph (name : String) (adjacency : BinaryFractionalWalkOracle.Adjacency 3)
    (row : BinaryFractionalRows.Row 3) (ds : List (BinaryFractionalWalkOracle.Pair 3))
    (expected : Option ℕ) (demand : Option (BinaryFractionalWalkOracle.Pair 3)) : IO Unit := do
  let paths := (BinaryFractionalGraphOracle.collect adjacency row ds).1
  let selected := (BinaryFractionalGraphOracle.selected adjacency row ds).1
  unless selected.map (fun x => x.demand)==demand do
    throw (IO.userError ("FAILED actual graph oracle: "++name))
  check name (paths.map (fun x => x.path.cost)) expected

def chain : BinaryFractionalWalkOracle.Adjacency 3 :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => decide (i.val+1=j.val)))
def noEdges : BinaryFractionalWalkOracle.Adjacency 3 := Vector.replicate 3 (Vector.replicate 3 false)
def row (first : ℕ) : BinaryFractionalRows.Row 3 :=
  Vector.ofFn (fun i => if i.val=0 then frac first 0 else frac 1 0)
def demands : List (BinaryFractionalWalkOracle.Pair 3) := [(0,2),(1,2)]

end DirectedFlowCutGap.RetainedArgminSmoke
open DirectedFlowCutGap.RetainedArgminSmoke in
def main : IO Unit := do
  check "empty" [] none
  check "singleton" [frac 7 2] (some 0)
  check "first minimum" [frac 1 4,frac 1 1,frac 9 0] (some 0)
  check "middle minimum" [frac 5 1,frac 1 3,frac 3 1] (some 1)
  check "last minimum" [frac 2 0,frac 1 0,frac 0 6] (some 2)
  check "retain first equal" [frac 1 1,frac 2 3,frac 3 5] (some 0)
  check "new minimum then equal" [frac 1 0,frac 2 3,frac 1 1] (some 1)
  check "zero numerator ties" [frac 0 0,frac 0 7,frac 1 2] (some 0)
  let padded : DirectedFlowCutGap.BinaryRational.Fraction := ⟨[true,false,false],[false,true,false],by decide⟩
  check "padded equal costs retain pointer" [padded,frac 2 3,frac 3 5] (some 0)
  check "padded lower cost" [frac 3 3,padded,frac 5 7] (some 1)
  checkGraph "actual graph unreachable" noEdges (row 2) demands none none
  checkGraph "actual graph lower second path" chain (row 2) demands (some 1) (some (1,2))
  checkGraph "actual graph equal paths keep first" chain (Vector.replicate 3 (frac 0 0)) demands (some 0) (some (0,2))
