import DirectedFlowCutGap.GridFamilyProgram
import DirectedFlowCutGap.PackingGuardState

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation PackedBooleanConstructor

inductive Context {n : ℕ} (heap : NaturalHeap) (root : ℕ)
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (costs : BinaryFractionalRows.Row n)
    (xs : List DemandCollection.Demand) : Prop where
  | intro {costRoot graphRoot demandsRoot tail : ℕ} :
      heap[root]?=some (.pair costRoot tail) → heap[tail]?=some (.pair graphRoot demandsRoot) →
      WordPairTableRead.Table heap costRoot (IndexedRationalRead.fields costs.toList) →
      GraphAdjacencyProgram.Matrix heap graphRoot (GraphRelaxationRefinement.matrix adjacency) →
      DemandCollection.DemandList heap demandsRoot xs → Context heap root adjacency costs xs

theorem context_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ}
    {adjacency : BinaryFractionalWalkOracle.Adjacency n} {costs : BinaryFractionalRows.Row n}
    {xs : List DemandCollection.Demand} (h : Context heap root adjacency costs xs) (ext : NaturalHeap) :
    Context (heap++ext) root adjacency costs xs := by
  cases h with
  | intro first second costs graph demands =>
    exact .intro (lookup_extend first ext) (lookup_extend second ext)
      (BinaryIndexedPairRead.table_extend costs ext) (GraphAdjacencyProgram.matrix_extend graph ext)
      (DemandCollection.demands_extend demands ext)

theorem result_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {value : Option (BinaryFractionalCore.State n)}
    (h : MinimumGuess.Result heap root value) (ext : NaturalHeap) : MinimumGuess.Result (heap++ext) root value := by
  cases value with
  | none => exact lookup_extend h ext
  | some s => exact PackingStart.state_extend h ext

inductive StateList {n : ℕ} (heap : NaturalHeap) : ℕ → List (Option (BinaryFractionalCore.State n)) → Prop where
  | nil {root : ℕ} : heap[root]?=some .nil → StateList heap root []
  | cons {root head tail : ℕ} {s : Option (BinaryFractionalCore.State n)} {ss : List (Option (BinaryFractionalCore.State n))} :
      heap[root]?=some (.pair head tail) → MinimumGuess.Result heap head s → StateList heap tail ss →
      StateList heap root (s::ss)

theorem list_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {ss : List (Option (BinaryFractionalCore.State n))}
    (h : StateList heap root ss) (ext : NaturalHeap) : StateList (heap++ext) root ss := by
  induction h with
  | nil look => exact .nil (lookup_extend look ext)
  | cons look value _ ih => exact .cons (lookup_extend look ext) (result_extend value ext) ih
end DirectedFlowCutGap.GridFamily
