import DirectedFlowCutGap.ActualFinalDispatch
import DirectedFlowCutGap.PackedWordPairTable

/-! NEW, UNRUN physical degenerate fixtures. These execute the actual BitState
interpreter including its paid terminal attempt. They do not cover a positive
physical whole-program execution, and are not part of a source parser theorem. -/
namespace DirectedFlowCutGap.FinalDispatchSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

structure Trace (C : ℕ) where
  state : BitState C
  events : List Event
  operations : ℕ
  terminalOperations : ℕ
  instructions : ℕ
  halted : Bool

/-- Tail recursion keeps one current heap, numeric totals and reversed events.
No recursive return retains previous full interpreter states or heap versions. -/
def execute {C : ℕ} (p : Program C) (fuel : ℕ) (s : BitState C) : Trace C :=
  go fuel s [] 0 0
where
  go : ℕ → BitState C → List Event → ℕ → ℕ → Trace C
  | 0,s,events,operations,instructions => ⟨s,events.reverse,operations,0,instructions,false⟩
  | fuel+1,s,events,operations,instructions =>
      let a := attempt p s
      match a.result with
      | none => ⟨s,events.reverse,operations+a.operations,a.operations,instructions,true⟩
      | some r => go fuel r.state (r.events.reverse++events) (operations+a.operations) (instructions+1)

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
  return (←readBits heap (heap.length+1) a,←readBits heap (heap.length+1) b)

def readTable (heap : NaturalHeap) : ℕ → ℕ → Option (List (Bits × Bits))
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      return (←readPair heap head)::(←readTable heap fuel tail)
    | _ => none

def readMatrix (heap : NaturalHeap) : ℕ → ℕ → Option (List Bits)
  | 0,_ => none
  | fuel+1,p => match heap[p]? with
    | some .nil => some []
    | some (.pair head tail) => do
      return (←readBits heap (heap.length+1) head)::(←readMatrix heap fuel tail)
    | _ => none

def pairTable : List (Bits × Bits) → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | pair::pairs,s => PackedWordPairTable.prepend pair (pairTable pairs s)

def wordList : List Bits → PackedWordPairTable.Prepared → PackedWordPairTable.Prepared
  | [],s => PackedWordPairTable.allocate .nil s
  | word::words,s =>
    let tail := wordList words s
    let head := PackedWordPairTable.word word tail
    PackedWordPairTable.allocate (.pair head.root tail.root) head

inductive Expected where
  | infeasible (demand : Bits × Bits)
  | zero (mask : Bits)

def correctOutput (heap : NaturalHeap) (root : ℕ) (expected : Expected) : Bool :=
  match heap[root]? with
  | some (.pair tag payload) => match expected with
    | .infeasible demand => heap[tag]?==some (.flag false) && readPair heap payload==some demand
    | .zero mask => heap[tag]?==some (.flag true) && readBits heap (heap.length+1) payload==some mask
  | _ => false

/-- Only original cost/matrix/demand roots are packed. Neither generated labels,
dispatch context, child outputs nor branch witnesses are supplied to the run. -/
def check (name : String) (cs : List (Bits × Bits)) (rows : List Bits)
    (ds : List (Bits × Bits)) (expected : Expected) : IO Unit := do
  IO.println ("BEGIN final dispatcher physical degenerate "++name)
  (←IO.getStdout).flush
  let costs := pairTable cs PackedWordPairTable.seed
  let matrix := wordList rows costs
  let demands := pairTable ds matrix
  let source : Bits := [true,false,true]
  let initial : BitState 13320 := ⟨demands.heap,demands.next,
    ⟨costs.root,matrix.root,demands.root,[]⟩,[],13318,source⟩
  let labels := RowVertexScan.words cs.length []
  -- Exact successful-instruction count for an early (infeasible/zero) return:
  -- row enumeration + original dispatch body + 16 composition instructions.
  let count := RowVertexScan.steps cs.length []+4*cs.length+9+
    OriginalDispatch.steps labels cs rows ds+16
  let actual := execute FinalDispatch.program (count+1) initial
  let heap := (eraseState actual.state).heap
  let regs := (eraseState actual.state).registers
  let endAttempt := attempt FinalDispatch.program actual.state
  let preserved :=
    actual.state.registers.a==initial.registers.a &&
    actual.state.registers.b==initial.registers.b &&
    actual.state.registers.c==initial.registers.c &&
    readTable heap (heap.length+1) regs.a==some cs &&
    readMatrix heap (heap.length+1) regs.b==some rows &&
    readTable heap (heap.length+1) regs.c==some ds &&
    actual.state.heap.take initial.heap.length==initial.heap &&
    heap.take (eraseState initial).heap.length==(eraseState initial).heap
  unless actual.halted && correctOutput heap regs.d expected && preserved &&
      actual.instructions==count && actual.state.pc==13319 &&
      actual.state.stack.isEmpty && actual.state.source==source && actual.events.isEmpty &&
      value initial.next==initial.heap.length && value actual.state.next==actual.state.heap.length &&
      endAttempt.result.isNone && actual.terminalOperations==endAttempt.operations &&
      actual.terminalOperations==controlCost 13320 && actual.terminalOperations ≤ actual.operations do
    throw (IO.userError ("FAIL final dispatcher physical degenerate "++name++
      " pc="++toString actual.state.pc.val++" instructions="++toString actual.instructions++
      " expectedInstructions="++toString count++" heap="++toString heap.length))
  IO.println ("PASS final dispatcher physical degenerate "++name++
    " instructions="++toString actual.instructions++" physicalOperationsIncludingHalt="++
    toString actual.operations++" terminalOperations="++toString actual.terminalOperations)

def main (args : List String) : IO Unit := do
  let selected := args.headD "all"
  if selected=="all" || selected=="empty" then
    check "empty" [] [] [] (.zero [])
  if selected=="all" || selected=="one-zero-no-demands" then
    check "one-zero-no-demands" [([],[true])] [[false]] [] (.zero [true])
  if selected=="all" || selected=="self-demand" then
    check "self-demand" [([],[true])] [[false]] [([],[])] (.infeasible ([],[]))
  if selected=="all" || selected=="two-unit-direct" then
    check "two-unit-direct" [([true],[true]),([true],[true])]
      [[false,true],[false,false]] [([],[true])] (.infeasible ([],[true]))
  unless ["all","empty","one-zero-no-demands","self-demand","two-unit-direct"].contains selected do
    throw (IO.userError "unknown final-dispatch physical degenerate fixture")
end DirectedFlowCutGap.FinalDispatchSmoke

def main := DirectedFlowCutGap.FinalDispatchSmoke.main
