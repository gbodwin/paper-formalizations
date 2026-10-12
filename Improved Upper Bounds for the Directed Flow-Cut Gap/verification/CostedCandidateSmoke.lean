import DirectedFlowCutGap.MaterializedGraphSelection
import DirectedFlowCutGap.PackedWordPairTable
namespace DirectedFlowCutGap.CostedCandidateSmoke
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open CostedCandidateMaterialization BinaryFractionalRows
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

def checkCommon {C : ℕ} (name : String) (initial : BitState C) (t : Trace C) (steps cells : ℕ) : IO Unit := do
  unless t.halted && t.events.isEmpty && t.state.source==initial.source &&
      t.state.stack.isEmpty && t.state.heap.take initial.heap.length==initial.heap &&
      t.state.heap.length==initial.heap.length+cells &&
      value t.state.next==t.state.heap.length &&
      t.operations ≤ completeBound C (initial.heap.length+1) (initial.heap.length+1) steps do
    throw (IO.userError ("FAILED materialized-cost machine invariants: "++name))

def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | w::ws,s =>
    let t := wordList ws s
    let h := PackedWordPairTable.word w t
    PackedWordPairTable.allocate (.pair h.root t.root) h


structure Spec where
  words : List Bits
  sourceWord : Bits
  payload : Bits

def prepare : List Spec → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared × List Candidate
  | [],s => (PackedWordPairTable.allocate .nil s,[])
  | x::xs,s =>
    let tail := prepare xs s
    let path := wordList x.words tail.1
    let sw := PackedWordPairTable.word x.sourceWord path
    let payload := PackedWordPairTable.word x.payload sw
    let metadata := PackedWordPairTable.allocate (.pair sw.root payload.root) payload
    let record := PackedWordPairTable.allocate (.pair path.root metadata.root) metadata
    let outer := PackedWordPairTable.allocate (.pair record.root tail.1.root) record
    (outer,⟨x.words,x.sourceWord,value payload.root⟩::tail.2)

def readItems (heap : NaturalHeap) : ℕ → ℕ → Option (List ((Bits×Bits)×ℕ×ℕ))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      let some (.pair cost payload) := heap[head]? | none
      let x ← readFraction heap cost
      let xs ← readItems heap fuel tail
      return (x,payload,head)::xs
    | _ => none

def observation (x : RetainedArgminProgram.Item) : (Bits×Bits)×ℕ×ℕ :=
  ((x.score.num,x.score.den),x.payload,x.address)

def checkPrepared (name : String) (rows : List Fraction) (table : Bits)
    (built : PackedWordPairTable.Prepared) (xs : List Candidate) (expected : Option ℕ) : IO Unit := do
  let initial : BitState 307 := ⟨built.heap,built.next,⟨built.root,table,[],[]⟩,[],305,[true,false,true,false]⟩
  let expectedItems := items rows (value built.next) xs
  let msteps := CostedCandidateMaterialization.steps rows xs+1
  let mat := execute CostedCandidateMaterialization.program (msteps+1) initial
  checkCommon (name++" collection") initial mat msteps (CostedCandidateMaterialization.cells rows xs)
  unless mat.state.pc==306 && readItems (eraseState mat.state).heap (mat.state.heap.length+1)
      (value mat.state.registers.d)==some (expectedItems.map observation) do
    throw (IO.userError ("FAILED actual costed list: "++name))
  IO.println ("PASS actual candidate collection "++name)
  let input : BitState 501 := ⟨built.heap,built.next,⟨built.root,table,[],[]⟩,[],305,[false,true,true]⟩
  let steps := CostedCandidateSelection.steps rows (value built.next) xs
  let t := execute CostedCandidateSelection.program (steps+1) input
  let heap := (eraseState t.state).heap
  let selectedOK : Bool := match expected with
    | none => heap[value t.state.registers.d]?==some .nil && t.state.pc==482
    | some i => match expectedItems[i]? with
      | none => false
      | some x => value t.state.registers.d==x.address && t.state.pc==484 &&
          (match heap[x.address]? with
          | some (.pair cost p) => p==x.payload && readFraction heap cost==some (x.score.num,x.score.den)
          | _ => false)
  checkCommon (name++" selection") input t steps (CostedCandidateSelection.cells rows (value built.next) xs)
  unless selectedOK do throw (IO.userError ("FAILED actual materialized selection: "++name))
  IO.println ("PASS actual materialized selection "++name)

def check (name : String) (rows : List Fraction) (specs : List Spec) (expected : Option ℕ) : IO Unit := do
  let table := PackedWordPairTable.construct (rows.map fun x => (x.num,x.den))
  let (built,xs) := prepare specs table
  checkPrepared name rows table.root built xs expected

def frac (n d : ℕ) : Fraction := ⟨n.bits,(d+1).bits,by simp [value_bits]⟩
def path (source : ℕ) (tails : List ℕ) (payload : ℕ) : Spec :=
  ⟨tails.map Nat.bits,source.bits,payload.bits⟩
def rows : List Fraction := [frac 5 2,frac 1 1,frac 2 4]

def duplicate : IO Unit := do
  let table := PackedWordPairTable.construct (rows.map fun x => (x.num,x.den))
  let (built,xs) := prepare [path 0 [1,2] 7] table
  let some (.pair head _) := (eraseHeap built.heap)[value built.root]? | throw (IO.userError "invalid fixture setup")
  let repeated := PackedWordPairTable.allocate (.pair head.bits built.root) built
  checkPrepared "identical occurrence payloads have distinct output addresses" rows table.root repeated (xs++xs) (some 0)

def chain : BinaryFractionalWalkOracle.Adjacency 3 :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => decide (i.val+1=j.val)))
def noEdges : BinaryFractionalWalkOracle.Adjacency 3 := Vector.replicate 3 (Vector.replicate 3 false)
def graphRow (first : ℕ) : Row 3 := Vector.ofFn (fun i => if i.val=0 then frac first 0 else frac 1 0)
def demands : List (BinaryFractionalWalkOracle.Pair 3) := [(0,2),(1,2)]

def checkGraph (name : String) (adj : BinaryFractionalWalkOracle.Adjacency 3) (row : Row 3)
    (expected : Option ℕ) (demand : Option (BinaryFractionalWalkOracle.Pair 3)) : IO Unit := do
  let paths := (BinaryFractionalGraphOracle.collect adj row demands).1
  let selected := (BinaryFractionalGraphOracle.selected adj row demands).1
  unless selected.map (fun q => q.demand)==demand do throw (IO.userError ("bad graph expectation "++name))
  let specs := paths.map fun q => path q.demand.1.val (q.path.edges.map fun e => e.1.val) q.demand.1.val
  check name row.toList specs expected

def main : IO Unit := do
  check "empty graph and collection" [] [] none
  check "single source-zero path" rows [path 0 [0] 10] (some 0)
  check "first minimum" rows [path 0 [2] 11,path 0 [1] 12] (some 0)
  check "last minimum" rows [path 0 [1] 13,path 0 [2] 14] (some 1)
  check "middle minimum" rows [path 2 [0] 15,path 0 [2] 16,path 0 [1,2] 17] (some 1)
  check "equal scores retain original payload" rows [path 0 [1,2] 18,path 0 [2,1] 19] (some 0)
  check "unequal stored fractions tie" [frac 0 0,frac 1 1,frac 2 3]
    [path 0 [1] 25,path 0 [2] 26] (some 0)
  check "empty paths retain first" rows [path 0 [] 20,path 2 [] 21] (some 0)
  check "different source conventions" rows [path 1 [0,1] 22,path 0 [0,1] 23] (some 1)
  check "padded source and index equality" rows [⟨[[false,false]], [false], [true,false]⟩,path 0 [1] 24] (some 0)
  duplicate
  checkGraph "actual graph unreachable" noEdges (graphRow 2) none none
  checkGraph "actual graph second demand" chain (graphRow 2) (some 1) (some (1,2))
  checkGraph "actual graph equal costs" chain (Vector.replicate 3 (frac 0 0)) (some 0) (some (0,2))
  IO.println "COSTED_CANDIDATE_ACTUAL_FIXTURES passed: 28 cases"
end DirectedFlowCutGap.CostedCandidateSmoke

def main : IO Unit := DirectedFlowCutGap.CostedCandidateSmoke.main
