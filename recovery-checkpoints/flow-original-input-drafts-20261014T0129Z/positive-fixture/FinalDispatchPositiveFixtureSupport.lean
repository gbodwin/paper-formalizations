import DirectedFlowCutGap.ActualFinalDispatch
import DirectedFlowCutGap.PackedWordPairTable

/-! NEW UNRUN TEST SUPPORT. Source inspection only: no Lean/compiler invocation.
The initial store packs original costs, adjacency rows and demands, and nothing
else. Decoders and the high-level oracle are observation-side test code. -/
namespace DirectedFlowCutGap.FinalDispatchPositiveFixture
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead BinaryRational

-- A smallest positive-dispatch example: no self/direct demand, and the only
-- internal vertex has positive cost. Zero-cost endpoints remain retained.
def adjacency : BinaryFractionalWalkOracle.Adjacency 3 :=
  Vector.ofFn fun i => Vector.ofFn fun j => decide (i.val + 1 = j.val)

def costs : BinaryFractionalRows.Row 3 :=
  Vector.ofFn fun i => if i.val == 1 then one else zero

def demands : List (BinaryFractionalWalkOracle.Pair 3) := [(0,2)]

def input : BinaryFractionalGuesses.Input 3 := ⟨adjacency,demands,costs⟩
def source : Bits := [true,false,true]
def costFields := IndexedRationalRead.fields costs.toList
def rows := GraphRelaxationRefinement.matrix adjacency
def demandFields := demands.map fun e =>
  (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2)

def pairTable : List (Bits × Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | pair::pairs,s => PackedWordPairTable.prepend pair (pairTable pairs s)

def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | word::words,s =>
      let tail := wordList words s
      let head := PackedWordPairTable.word word tail
      PackedWordPairTable.allocate (.pair head.root tail.root) head

/-- No generated vertices, dispatch context, minimum, exponent, grid fuel,
branch witness, child output or expected state is inserted into the store. -/
def initial : BitState 13320 :=
  let cs := pairTable costFields PackedWordPairTable.seed
  let matrix := wordList rows cs
  let ds := pairTable demandFields matrix
  ⟨ds.heap,ds.next,⟨cs.root,matrix.root,ds.root,[]⟩,[],13318,source⟩

def readBits (heap : NaturalHeap) : ℕ → ℕ → Option Bits
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => match heap[head]? with
      | some (.flag b) => (readBits heap fuel tail).map (b::·)
      | _ => none
    | _ => none

def readPair (heap : NaturalHeap) (root : ℕ) : Option (Bits × Bits) := do
  let .pair a b ← heap[root]? | none
  return (← readBits heap (heap.length+1) a,← readBits heap (heap.length+1) b)

def readTable (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits × Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      return (← readPair heap head)::(← readTable heap fuel tail)
    | _ => none

def readMatrix (heap : NaturalHeap) : ℕ → ℕ → Option (List Bits)
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      return (← readBits heap (heap.length+1) head)::(← readMatrix heap fuel tail)
    | _ => none

def readEvents (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits × Bits × (Bits × Bits)))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair event tail) => do
      let .pair choice amount ← heap[event]? | none
      let .pair mask index ← heap[choice]? | none
      let entry := (← readBits heap (heap.length+1) mask,
        ← readBits heap (heap.length+1) index,← readPair heap amount)
      return entry::(← readEvents heap fuel tail)
    | _ => none

abbrev RawState := List (Bits × Bits) × List (Bits × Bits) × (Bits × Bits) ×
  (Bits × Bits) × List (Bits × Bits) × List (Bits × Bits × (Bits × Bits))

def readState (heap : NaturalHeap) (root : ℕ) : Option RawState := do
  let .pair yr k1 ← heap[root]? | none
  let .pair wr k2 ← heap[k1]? | none
  let .pair cr k3 ← heap[k2]? | none
  let .pair zr k4 ← heap[k3]? | none
  let .pair lr er ← heap[k4]? | none
  return (← readTable heap (heap.length+1) yr,← readTable heap (heap.length+1) wr,
    ← readPair heap cr,← readPair heap zr,← readTable heap (heap.length+1) lr,
    ← readEvents heap (heap.length+1) er)

/-- Preserve order and fail on a missing/invalid state. A positive covers output
cannot use a nil child as a substitute for a computed state. -/
def readStates (heap : NaturalHeap) : ℕ → ℕ → Option (List RawState)
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      return (← readState heap head)::(← readStates heap fuel tail)
    | _ => none

def readCovers (heap : NaturalHeap) (root : ℕ) : Option (List RawState) := do
  let .pair tag states ← heap[root]? | none
  let .nil ← heap[tag]? | none
  readStates heap (heap.length+1) states

def fields (xs : List Fraction) := xs.map fun x => (x.num,x.den)

def raw {n : ℕ} (s : BinaryFractionalCore.State n) : RawState :=
  (fields s.weights.toList,fields s.best.toList,(s.bestCost.num,s.bestCost.den),
    (s.total.num,s.total.den),fields s.loads.toList,
    s.events.map fun e => (e.choice.mask.toList,RowVertices.vertexLabel e.choice.bottleneck,
      (e.amount.num,e.amount.den)))

/-- Observation-side oracle only. This is never supplied to an interpreter.
Compare every stored state field, all bits and the exact ordered event list;
Result.operations, stopTests and other Result metadata are not output fields. -/
def expectedStates : IO (List RawState) := do
  match (BinaryFractionalGuesses.solveInput input).1 with
  | .covers results => return results.map fun r => raw r.state
  | .infeasible _ => throw (IO.userError "fixture oracle unexpectedly selected infeasible")
  | .zero _ => throw (IO.userError "fixture oracle unexpectedly selected zero")
  | .invalid => throw (IO.userError "fixture oracle unexpectedly selected invalid")

structure Visits where
  dispatch : Bool := false
  positive : Bool := false
  minimum : Bool := false
  gridCall : Bool := false
  gridEntry : Bool := false
  wrapped : Bool := false
  deriving Repr

def Visits.observe (v : Visits) (pc : ℕ) : Visits :=
  ⟨v.dispatch || pc == 12898,v.positive || pc == 13306,v.minimum || pc == 13262,
    v.gridCall || pc == 13309,v.gridEntry || pc == 10758,v.wrapped || pc == 13311⟩

def Visits.complete (v : Visits) : Bool :=
  v.dispatch && v.positive && v.minimum && v.gridCall && v.gridEntry && v.wrapped

def checkOriginalRoots (before after : NaturalState 13320) : Bool :=
  after.registers.a == before.registers.a &&
  after.registers.b == before.registers.b &&
  after.registers.c == before.registers.c &&
  readTable after.heap (after.heap.length+1) after.registers.a == some costFields &&
  readMatrix after.heap (after.heap.length+1) after.registers.b == some rows &&
  readTable after.heap (after.heap.length+1) after.registers.c == some demandFields &&
  after.heap.take before.heap.length == before.heap

/-- Cheap branch/original-input guard. It does not compute child grid outputs
or replace the physical positive-branch observations in the final check. -/
def preflight : IO Unit := do
  let labels := List.ofFn (RowVertices.vertexLabel (n := 3))
  unless costFields == [([],[true]),([true],[true]),([],[true])] &&
      rows == [[false,true,false],[false,false,true],[false,false,false]] &&
      demandFields == [([],[false,true])] do
    throw (IO.userError "literal original fixture fields changed")
  match OriginalDispatch.result labels costFields rows demandFields with
  | .positive _ => pure ()
  | _ => throw (IO.userError "OriginalDispatch did not select the positive branch")
  match (BinaryFractionalDispatch.dispatch adjacency demands costs).1 with
  | .positive _ => pure ()
  | _ => throw (IO.userError "high-level dispatch did not select the positive branch")
  unless (BinaryFractionalDispatch.minimumPositive costs).1 == some (1 : Fin 3) do
    throw (IO.userError "fixture positive minimum changed")
  let gridEntries := value (BinaryFractionalGuesses.gridFuel
    (BinaryFractionalCore.dimension costs).1 (BinaryFractionalGuesses.inputWidth costs).1).1
  unless gridEntries == 9 do
    throw (IO.userError "fixture grid size changed")
  IO.println ("PREFLIGHT_ONLY positive chain 0->1->2; demand 0->2; costs [0,1,0]; gridEntries=" ++
    toString gridEntries ++ "; innerStopTestsPerEntry=27")
  (← IO.getStdout).flush

/-- Every executable requires an explicit cap; no speculative default run. -/
def parseCap (args : List String) : IO ℕ := do
  match args with
  | [cap] => match cap.toNat? with
    | some n =>
      if n == 0 then throw (IO.userError "attempt cap must be positive") else return n
    | none => throw (IO.userError "attempt cap must be a natural number")
  | _ => throw (IO.userError "provide exactly one explicit maximum-attempt count")

end DirectedFlowCutGap.FinalDispatchPositiveFixture
