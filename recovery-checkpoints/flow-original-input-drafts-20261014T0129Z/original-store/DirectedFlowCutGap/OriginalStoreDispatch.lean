import DirectedFlowCutGap.OriginalStoreInitial
import DirectedFlowCutGap.FinalDispatchEnvelope

/-!
UNVERIFIED ADDITIVE DRAFT, 2026-10-14. No Lean compilation has been run.
The imported dispatcher and envelope are reconstructed drafts, not recovered
published sources. All their strict/replay results must be checked separately.

The Boolean/list preparation charge is added to the physical dispatch run and
its terminal attempt. This does not turn preparation into an instruction trace.
The covers branch retains exactly the existing ordered state projection, not
all fields of the high-level Result records.
-/
noncomputable section

namespace DirectedFlowCutGap.OriginalStoreDispatch
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open OriginalStoreInitial OriginalStoreInputViews Polynomial

/-- Concrete typed-input initialization discharges every represented-store,
dense-cursor, empty-stack and initial H/B premise of the fixed dispatcher. -/
theorem solve_original_bit {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    ∃ xs k charge out,
      List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds ∧
      Run FinalDispatch.program k charge (prepare adjacency costs ds).1 [] out ∧
      FinalDispatch.Output (eraseState out).heap (eraseState out).registers.d
        (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ∧
      WordPairTableRead.Table (eraseState out).heap
        (eraseState (prepare adjacency costs ds).1).registers.a
        (IndexedRationalRead.fields costs.toList) ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap
        (eraseState (prepare adjacency costs ds).1).registers.b
        (GraphRelaxationRefinement.matrix adjacency) ∧
      DemandCollection.DemandList (eraseState out).heap
        (eraseState (prepare adjacency costs ds).1).registers.c xs ∧
      (eraseState out).registers.a=(eraseState (prepare adjacency costs ds).1).registers.a ∧
      (eraseState out).registers.b=(eraseState (prepare adjacency costs ds).1).registers.b ∧
      (eraseState out).registers.c=(eraseState (prepare adjacency costs ds).1).registers.c ∧
      out.source=[] ∧ out.stack=[] ∧ out.pc=13319 ∧ value out.next=out.heap.length ∧
      (∃ ext,(eraseState out).heap=(eraseState (prepare adjacency costs ds).1).heap++ext) ∧
      (attempt FinalDispatch.program out).result=none ∧
      (prepare adjacency costs ds).2+charge+(attempt FinalDispatch.program out).operations ≤
        preparationBound adjacency costs ds+
          completeBound 13320 (heapCells adjacency costs ds+1) (heapCells adjacency costs ds)
            (FinalDispatch.inputBound adjacency costs ds) := by
  obtain ⟨xs,encoded,bounded,pc0,empty,source,dense,table,graph,pairs,prepCharge⟩ :=
    OriginalStoreInitial.prepare_spec adjacency costs ds
  obtain ⟨k,charge,out,run,rep,tableOut,graphOut,pairsOut,ra,rb,rc,src,stack,pc,next,ext,stop,cost⟩ :=
    FinalDispatch.solve_bit adjacency costs encoded (prepare adjacency costs ds).1
      bounded pc0 dense empty table graph pairs
  refine ⟨xs,k,charge,out,encoded,run,rep,tableOut,graphOut,pairsOut,ra,rb,rc,
    src.trans source,stack,pc,next,ext,stop,?_⟩
  omega

/-- One explicit envelope for the typed-input view allowances. -/
def viewPolynomial : Polynomial ℕ :=
  16*X+8*X^2+X*(32*(X+1)^2+12)+12

theorem view_le_eval {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    viewCharge adjacency costs ds ≤ viewPolynomial.eval (inputSize costs ds) := by
  let N := inputSize costs ds
  have hn : n ≤ N := by dsimp [N,inputSize];omega
  have hd : ds.length ≤ N := by dsimp [N,inputSize];omega
  have demandBound := demandFields_charge ds
  have first : viewCharge adjacency costs ds ≤
      16*n+8*n*n+ds.length*(32*(n+1)^2+12)+12 := by
    unfold viewCharge costFields matrixFields
    simp only [Vector.length_toList,GraphRelaxationRefinement.matrix_length]
    change 8*n+4+(8*n+8*PackedOriginalStore.rowBits (matrixWords adjacency)+4)+
      (demandFields ds).2 ≤ _
    rw [matrix_storedBits]
    simp only [Nat.mul_assoc] at *
    omega
  calc
    viewCharge adjacency costs ds ≤
        16*n+8*n*n+ds.length*(32*(n+1)^2+12)+12 := first
    _ ≤ viewPolynomial.eval N := by
      simp only [viewPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
        Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,pow_two,Nat.mul_assoc]
      gcongr

def preparationPolynomial : Polynomial ℕ :=
  64*(32*X^2)^3+24*(32*X^2)+53+viewPolynomial

theorem preparation_le_eval {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    preparationBound adjacency costs ds ≤ preparationPolynomial.eval (inputSize costs ds) := by
  have hL := heapCells_bound adjacency costs ds
  have hv := view_le_eval adjacency costs ds
  unfold preparationBound preparationPolynomial
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_X]
  gcongr

/-- A single diagonal majorant bounds original dimensions and initial H/B. -/
def diagonalPolynomial : Polynomial ℕ := 32*X^2+2*X+2

def totalPolynomial : Polynomial ℕ := preparationPolynomial+
  FinalDispatchEnvelope.physicalPolynomial.comp diagonalPolynomial

/-- This polynomial bounds preparation's declared Boolean/list charge plus
exactly the same physical dispatch run and its paid terminal attempt. There is
still no claim of one finite-instruction run from an unparsed external input. -/
theorem solve_original_polynomial_bit {n : ℕ}
    (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    ∃ k charge out,
      Run FinalDispatch.program k charge (prepare adjacency costs ds).1 [] out ∧
      FinalDispatch.Output (eraseState out).heap (eraseState out).registers.d
        (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ∧
      out.source=[] ∧ out.stack=[] ∧ out.pc=13319 ∧ value out.next=out.heap.length ∧
      (attempt FinalDispatch.program out).result=none ∧
      (prepare adjacency costs ds).2+charge+(attempt FinalDispatch.program out).operations ≤
        totalPolynomial.eval (inputSize costs ds) := by
  obtain ⟨xs,k,charge,out,encoded,run,rep,table,graph,pairs,ra,rb,rc,source,stack,pc,dense,ext,stop,total⟩ :=
    solve_original_bit adjacency costs ds
  let N := inputSize costs ds
  have hn : n ≤ N := by dsimp [N,inputSize];omega
  have hd : ds.length ≤ N := by dsimp [N,inputSize];omega
  have hs : LambdaRowProgram.rowBits costs.toList ≤ N := by dsimp [N,inputSize];omega
  have hL := heapCells_bound adjacency costs ds
  have diagonal : diagonalPolynomial.eval N=32*N^2+2*N+2 := by
    simp only [diagonalPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_ofNat,Polynomial.eval_X]
  have physical := FinalDispatchEnvelope.physical_le_eval adjacency costs ds
    (N:=diagonalPolynomial.eval N)
    (H:=heapCells adjacency costs ds+1) (B:=heapCells adjacency costs ds)
    (by rw [diagonal];omega) (by rw [diagonal];omega) (by rw [diagonal];omega)
    (by rw [diagonal];omega) (by rw [diagonal];omega)
  have preparation := preparation_le_eval adjacency costs ds
  refine ⟨k,charge,out,run,rep,source,stack,pc,dense,stop,?_⟩
  change _ ≤ totalPolynomial.eval N
  simp only [totalPolynomial,Polynomial.eval_add,Polynomial.eval_comp]
  omega

end DirectedFlowCutGap.OriginalStoreDispatch
