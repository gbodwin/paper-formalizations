import DirectedFlowCutGap.PackedOriginalStore
import DirectedFlowCutGap.LambdaRowProgram

/-!
UNVERIFIED ADDITIVE DRAFT, 2026-10-14. No Lean compilation has been run.

All represented input roots and initial H/B premises are generated from the
original typed adjacency, padded cost row and ordered demand list. The typed
Vector/Fin boundary is explicit; this is not a parser for external bytes.
-/
namespace DirectedFlowCutGap.OriginalStoreInitial
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedWordPairTable OriginalStoreInputViews

def costWords {n : ℕ} (costs : BinaryFractionalRows.Row n) : List (Bits × Bits) :=
  (costFields costs).1

def matrixWords {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n) : List Bits :=
  (matrixFields adjacency).1

def endpointWords {n : ℕ} (ds : List (BinaryFractionalWalkOracle.Pair n)) : List (Bits × Bits) :=
  (demandFields ds).1

def heapCells {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  PackedOriginalStore.cells (costWords costs) (matrixWords adjacency) (endpointWords ds)

/-- One typed-input front end, including label generation and paid installation.
All fields are evaluated by the displayed bodies. The extra 16 is a declared
fixed allowance for this outer tuple/record assembly. -/
def prepare {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    BitState 13320 × ℕ :=
  let c := costFields costs
  let m := matrixFields adjacency
  let d := demandFields ds
  let p := PackedOriginalStore.prepare c.1 m.1 d.1
  (p.1,p.2+c.2+m.2+d.2+16)

def preparationBound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  64*(heapCells adjacency costs ds)^3+24*heapCells adjacency costs ds+53+
    viewCharge adjacency costs ds

/-- Zero initial-state premises remain. Demand addresses are existential
specification witnesses with the original order and multiplicity preserved. -/
theorem prepare_spec {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    ∃ xs,
      List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds ∧
      (prepare adjacency costs ds).1.Bounded
        (heapCells adjacency costs ds+1) (heapCells adjacency costs ds) ∧
      (prepare adjacency costs ds).1.pc=13318 ∧
      (prepare adjacency costs ds).1.stack=[] ∧ (prepare adjacency costs ds).1.source=[] ∧
      value (prepare adjacency costs ds).1.next=(prepare adjacency costs ds).1.heap.length ∧
      WordPairTableRead.Table (eraseState (prepare adjacency costs ds).1).heap
        (eraseState (prepare adjacency costs ds).1).registers.a
        (IndexedRationalRead.fields costs.toList) ∧
      GraphAdjacencyProgram.Matrix (eraseState (prepare adjacency costs ds).1).heap
        (eraseState (prepare adjacency costs ds).1).registers.b
        (GraphRelaxationRefinement.matrix adjacency) ∧
      DemandCollection.DemandList (eraseState (prepare adjacency costs ds).1).heap
        (eraseState (prepare adjacency costs ds).1).registers.c xs ∧
      (prepare adjacency costs ds).2 ≤ preparationBound adjacency costs ds := by
  obtain ⟨bounded,pc,stack,source,dense,table,matrix,demands,charge⟩ :=
    PackedOriginalStore.prepare_spec (costWords costs) (matrixWords adjacency) (endpointWords ds)
  have dt : WordPairTableRead.Table
      (eraseState (prepare adjacency costs ds).1).heap
      (eraseState (prepare adjacency costs ds).1).registers.c
      (ds.map fun d => (RowVertices.vertexLabel d.1,RowVertices.vertexLabel d.2)) := by
    simpa only [prepare,costWords,matrixWords,endpointWords,demandFields_exact] using demands
  obtain ⟨xs,pairs,encoded⟩ :=
    PackedOriginalStore.table_demands RowVertices.vertexLabel ds dt
  refine ⟨xs,encoded,bounded,pc,stack,source,dense,table,matrix,pairs,?_⟩
  change (PackedOriginalStore.prepare (costWords costs) (matrixWords adjacency) (endpointWords ds)).2+
      (costFields costs).2+(matrixFields adjacency).2+(demandFields ds).2+16 ≤ _
  unfold preparationBound heapCells viewCharge
  omega

theorem heap_length {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    (prepare adjacency costs ds).1.heap.length=heapCells adjacency costs ds := by
  exact (PackedOriginalStore.construct_spec
    (costWords costs) (matrixWords adjacency) (endpointWords ds)).length

theorem cost_storedBits {n : ℕ} (costs : BinaryFractionalRows.Row n) :
    storedBits (costWords costs)=LambdaRowProgram.rowBits costs.toList := by
  change storedBits (IndexedRationalRead.fields costs.toList)=_
  generalize costs.toList=rows
  induction rows with
  | nil => rfl
  | cons q qs ih =>
      change q.num.length+q.den.length+storedBits (IndexedRationalRead.fields qs)=
        q.num.length+q.den.length+LambdaRowProgram.rowBits qs
      rw [ih]

theorem matrix_storedBits {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n) :
    PackedOriginalStore.rowBits (matrixWords adjacency)=n*n := by
  simp [PackedOriginalStore.rowBits,matrixWords,matrixFields,
    GraphRelaxationRefinement.matrix,List.map_map,Function.comp_def]

theorem endpoint_storedBits {n : ℕ} (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    storedBits (endpointWords ds) ≤ 2*ds.length*n := by
  unfold endpointWords
  rw [demandFields_exact]
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hs := RowVertices.label_width d.1
      have ht := RowVertices.label_width d.2
      simp only [List.map_cons,storedBits_cons,List.length_cons]
      nlinarith

/-- Exact physical cell count retains every stored rational and endpoint bit. -/
theorem heapCells_exact {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    heapCells adjacency costs ds=
      3+6*n+2*LambdaRowProgram.rowBits costs.toList+2*n*n+
        4*ds.length+2*storedBits (endpointWords ds) := by
  have hc : (costWords costs).length=n := by
    simp [costWords,costFields,IndexedRationalRead.fields]
  have hm : (matrixWords adjacency).length=n := GraphRelaxationRefinement.matrix_length adjacency
  have hd : (endpointWords ds).length=ds.length := by
    simp [endpointWords,demandFields_exact]
  unfold heapCells PackedOriginalStore.cells
  rw [hc,hm,hd,cost_storedBits,matrix_storedBits]
  ring

/-- This size counts original dimensions, demand occurrences and every stored
cost digit, so padding can never disappear from the bound. -/
def inputSize {n : ℕ} (costs : BinaryFractionalRows.Row n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  n+ds.length+LambdaRowProgram.rowBits costs.toList+1

theorem heapCells_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    heapCells adjacency costs ds ≤ 32*(inputSize costs ds)^2 := by
  let N := inputSize costs ds
  have hn : n ≤ N := by dsimp [N,inputSize];omega
  have hd : ds.length ≤ N := by dsimp [N,inputSize];omega
  have hs : LambdaRowProgram.rowBits costs.toList ≤ N := by dsimp [N,inputSize];omega
  have hp : 1 ≤ N := by dsimp [N,inputSize];omega
  have linear : N ≤ N*N := by
    simpa using Nat.mul_le_mul_left N hp
  have hnn : n*n ≤ N*N := Nat.mul_le_mul hn hn
  have hdn : ds.length*n ≤ N*N := Nat.mul_le_mul hd hn
  have he := endpoint_storedBits ds
  rw [heapCells_exact]
  change _ ≤ 32*N^2
  nlinarith

end DirectedFlowCutGap.OriginalStoreInitial
