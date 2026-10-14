import DirectedFlowCutGap.ActualFinalDispatch
import DirectedFlowCutGap.SourcePackingPolynomialCosts

/-!
NEW reconstruction draft, 2026-10-14. This additive module was recreated from
published Flow722 sources after the unavailable local draft was lost. It is
not a recovered artifact and carries no elaboration claim until replayed.

One fixed polynomial majorizes the actual final dispatcher's input bound and
then the same represented-root physical run. Padded cost words are charged by
their stored lengths; generated labels and matrix cells have explicit bounds.
-/
noncomputable section

namespace DirectedFlowCutGap.FinalDispatchEnvelope
open BinaryArithmetic BinaryRational Polynomial
open ImmutableReferenceSimulation ImmutableReferenceTerminal SourcePackingPolynomial

/-- Uniform occurrence sum: repeated elements are counted on every occurrence. -/
theorem sum_map_le {α : Type*} (xs : List α) (f : α → ℕ) (b : ℕ)
    (bounded : ∀ x∈xs,f x≤b) : (xs.map f).sum≤xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head := bounded x (by simp)
    have tail := ih (fun y hy => bounded y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem fields_length (rows : List Fraction) :
    (IndexedRationalRead.fields rows).length=rows.length := by
  simp only [IndexedRationalRead.fields,List.length_map]

theorem fields_bits (rows : List Fraction) :
    SourceRowTableProgram.bits (IndexedRationalRead.fields rows)=LambdaRowProgram.rowBits rows := by
  induction rows with
  | nil => rfl
  | cons q qs ih =>
    change q.num.length+q.den.length+SourceRowTableProgram.bits (IndexedRationalRead.fields qs)=
      q.num.length+q.den.length+LambdaRowProgram.rowBits qs
    rw [ih]

theorem vertex_word_bits {n N : ℕ} (hn : n≤N) :
    ((List.ofFn (RowVertices.vertexLabel (n:=n))).map List.length).sum≤N*N := by
  have h := sum_map_le (List.ofFn (RowVertices.vertexLabel (n:=n))) List.length N (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact (RowVertices.label_width i).trans hn)
  simp only [List.length_ofFn] at h
  exact h.trans (Nat.mul_le_mul_right N hn)

theorem matrix_cells {n N : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (hn : n≤N) : ((GraphRelaxationRefinement.matrix adjacency).map List.length).sum≤N*N := by
  have h := sum_map_le (GraphRelaxationRefinement.matrix adjacency) List.length N (by
    intro row hr
    change row∈adjacency.toList.map (fun r => r.toList) at hr
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    simpa only [Vector.length_toList] using hn)
  rw [GraphRelaxationRefinement.matrix_length] at h
  exact h.trans (Nat.mul_le_mul_right N hn)

def emptyPolynomial : Polynomial ℕ := 26*(X+X+1)+6*X+6*(X*X)+40

def avoidingPolynomial : Polynomial ℕ :=
  (4*X+16*X+(32*(X*X)+(32*(X+X+2)+25)*X+4)+18)+
    (24*(X*X)+28*X+4)+11+
    (5*X+49+poly_GraphRecoveryController_instructionBound X (X+1) X)+11

def dispatchPolynomial : Polynomial ℕ :=
  X*(emptyPolynomial+12)+4+(X*(avoidingPolynomial+20)+4)+4*X+16*X+25

def instructionPolynomial : Polynomial ℕ :=
  poly_RowVertices_instructionBound X+dispatchPolynomial+
    GridFamilyEnvelope.minimumPolynomial+GridFamilyEnvelope.instructionPolynomial+32

theorem empty_le_eval {n N : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (s t : Fin n) (hn : n≤N) :
    EmptyDemandEdge.inputSteps (GraphRelaxationRefinement.matrix adjacency)
      (RowVertices.vertexLabel s) (RowVertices.vertexLabel t)≤emptyPolynomial.eval N := by
  have hs := (RowVertices.label_width s).trans hn
  have ht := (RowVertices.label_width t).trans hn
  have hm := matrix_cells adjacency hn
  unfold emptyPolynomial EmptyDemandEdge.inputSteps
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_one,Polynomial.eval_X,GraphRelaxationRefinement.matrix_length]
  gcongr

theorem avoiding_le_eval {n N : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (s t : Fin n)
    (hn : n≤N) (hS : LambdaRowProgram.rowBits costs.toList≤N) :
    AvoidingKeptPath.inputSteps (RowVertices.vertexLabel s) (RowVertices.vertexLabel t)
      (List.ofFn (RowVertices.vertexLabel (n:=n))) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (n+1)≤avoidingPolynomial.eval N := by
  have hs := (RowVertices.label_width s).trans hn
  have ht := (RowVertices.label_width t).trans hn
  have hv := vertex_word_bits hn
  have hm := matrix_cells adjacency hn
  have hg := bound_GraphRecoveryController_instructionBound N
    (N:=n) (W:=n+1) (S:=(RowVertices.vertexLabel s).length)
    (p_N:=X) (p_W:=X+1) (p_S:=X)
    (by simpa only [Polynomial.eval_X] using hn)
    (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      Nat.add_le_add_right hn 1)
    (by simpa only [Polynomial.eval_X] using hs)
  unfold avoidingPolynomial AvoidingKeptPath.inputSteps KeptAdjacencyInput.inputSteps
    KeptMaskInput.inputSteps KeptMask.inputSteps KeptMask.wordBits
    KeptAdjacencyMatrix.inputSteps KeptAdjacencyMatrix.rowCells AvoidingShortest.inputSteps
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_one,Polynomial.eval_X,List.length_ofFn,fields_length,
    Vector.length_toList,fields_bits,GraphRelaxationRefinement.matrix_length]
  gcongr

theorem dispatch_le_eval {n N : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (hd : ds.length≤N) (hn : n≤N) (hS : LambdaRowProgram.rowBits costs.toList≤N) :
    OriginalDispatch.inputSteps (List.ofFn (RowVertices.vertexLabel (n:=n)))
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2)) (n+1)≤
      dispatchPolynomial.eval N := by
  have he := sum_map_le ds
    (fun e => EmptyDemandEdge.inputSteps (GraphRelaxationRefinement.matrix adjacency)
      (RowVertices.vertexLabel e.1) (RowVertices.vertexLabel e.2)+12)
    (emptyPolynomial.eval N+12) (by
      intro e _
      exact Nat.add_le_add_right (empty_le_eval adjacency e.1 e.2 hn) 12)
  have ha := sum_map_le ds
    (fun e => AvoidingKeptPath.inputSteps (RowVertices.vertexLabel e.1) (RowVertices.vertexLabel e.2)
      (List.ofFn (RowVertices.vertexLabel (n:=n))) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (n+1)+20)
    (avoidingPolynomial.eval N+20) (by
      intro e _
      exact Nat.add_le_add_right (avoiding_le_eval adjacency costs e.1 e.2 hn hS) 20)
  have heb := he.trans (Nat.mul_le_mul_right (emptyPolynomial.eval N+12) hd)
  have hab := ha.trans (Nat.mul_le_mul_right (avoidingPolynomial.eval N+20) hd)
  unfold OriginalDispatch.inputSteps EmptyDemandScan.inputSteps AvoidingDemandScan.inputSteps
    dispatchPolynomial
  simp only [List.map_map,Function.comp_def,fields_bits,fields_length,Vector.length_toList,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

theorem minimum_le_eval {n N : ℕ} (costs : BinaryFractionalRows.Row n)
    (hn : n≤N) (hS : LambdaRowProgram.rowBits costs.toList≤N) :
    OriginalRowMinimum.inputSteps costs.toList≤GridFamilyEnvelope.minimumPolynomial.eval N := by
  rw [GridFamilyEnvelope.minimum_exact]
  unfold GridFamilyEnvelope.minimumBound GridFamilyEnvelope.minimumPolynomial RowVertices.instructionBound
  simp only [Vector.length_toList,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  gcongr

/-- The input expression is stated independently, then connected definitionally
below to the actual final dispatcher. It is not a substituted machine bound. -/
def originalInputBound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  RowVertices.instructionBound n+
    OriginalDispatch.inputSteps (List.ofFn (RowVertices.vertexLabel (n:=n)))
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2)) (n+1)+
    OriginalRowMinimum.inputSteps costs.toList+
    GridFamilyEnvelope.instructionBound ds.length n (LambdaRowProgram.rowBits costs.toList)+32

theorem original_le_eval {n N : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (hd : ds.length≤N) (hn : n≤N) (hS : LambdaRowProgram.rowBits costs.toList≤N) :
    originalInputBound adjacency costs ds≤instructionPolynomial.eval N := by
  have hv := bound_RowVertices_instructionBound N (n:=n) (p_n:=X)
    (by simpa only [Polynomial.eval_X] using hn)
  have hdispatch := dispatch_le_eval adjacency costs ds hd hn hS
  have hm := minimum_le_eval costs hn hS
  have hg := GridFamilyEnvelope.instruction_le_eval hd hn hS
  unfold originalInputBound instructionPolynomial
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

theorem input_bound_exact {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    FinalDispatch.inputBound adjacency costs ds=originalInputBound adjacency costs ds := rfl

theorem instruction_le_eval {n N : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (hd : ds.length≤N) (hn : n≤N) (hS : LambdaRowProgram.rowBits costs.toList≤N) :
    FinalDispatch.inputBound adjacency costs ds≤instructionPolynomial.eval N := by
  rw [input_bound_exact]
  exact original_le_eval adjacency costs ds hd hn hS

/-- This is the exact completeBound polynomial at the diagonal majorant,
including the successful prefix and the final terminal attempt. -/
def physicalPolynomial : Polynomial ℕ :=
  C (controlCost 13320+128)*instructionPolynomial*(X+X+2*instructionPolynomial+1)^2+
    C (controlCost 13320+128)*(X+instructionPolynomial+1)*(X+instructionPolynomial+1)

theorem physical_eval (N : ℕ) :
    physicalPolynomial.eval N=completeBound 13320 N N (instructionPolynomial.eval N) := by
  simp only [physicalPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,
    completeBound,runBound,stepBound]

theorem physical_le_eval {n H B N : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (hd : ds.length≤N) (hn : n≤N) (hS : LambdaRowProgram.rowBits costs.toList≤N)
    (hh : H≤N) (hb : B≤N) :
    completeBound 13320 H B (FinalDispatch.inputBound adjacency costs ds)≤physicalPolynomial.eval N := by
  rw [physical_eval]
  have bound := instruction_le_eval adjacency costs ds hd hn hS
  unfold completeBound runBound stepBound
  gcongr

theorem fixed_polynomial_bound : ∃ p : Polynomial ℕ,
    ∀ (n H B N : ℕ) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
      (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)),
      ds.length≤N → n≤N → LambdaRowProgram.rowBits costs.toList≤N → H≤N → B≤N →
      completeBound 13320 H B (FinalDispatch.inputBound adjacency costs ds)≤p.eval N :=
  ⟨physicalPolynomial,fun _ _ _ _ adjacency costs ds hd hn hS hh hb =>
    physical_le_eval adjacency costs ds hd hn hS hh hb⟩

/-- One fixed polynomial bounds the same physical dispatcher run at the
original-input measure. The covers branch retains the exact ordered state
projection specified by FinalDispatch.Output. No physical fixture is assumed. -/
theorem solve_fixed_polynomial_bit {n H B : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    (initial : BitState 13320) (bounded : initial.Bounded H B) (pc0 : initial.pc=13318)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a
      (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.b
      (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList (eraseState initial).heap (eraseState initial).registers.c xs) :
    ∃ k charge out,Run FinalDispatch.program k charge initial [] out ∧
      FinalDispatch.Output (eraseState out).heap (eraseState out).registers.d
        (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a
        (IndexedRationalRead.fields costs.toList) ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState initial).registers.b
        (GraphRelaxationRefinement.matrix adjacency) ∧
      DemandCollection.DemandList (eraseState out).heap (eraseState initial).registers.c xs ∧
      (eraseState out).registers.a=(eraseState initial).registers.a ∧
      (eraseState out).registers.b=(eraseState initial).registers.b ∧
      (eraseState out).registers.c=(eraseState initial).registers.c ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=13319 ∧ value out.next=out.heap.length ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt FinalDispatch.program out).result=none ∧
      charge+(attempt FinalDispatch.program out).operations ≤ physicalPolynomial.eval
        (ds.length+n+LambdaRowProgram.rowBits costs.toList+H+B+1) := by
  obtain ⟨k,charge,out,run,rep,tableOut,graphOut,pairsOut,ra,rb,rc,src,stack,pc,next,ext,stop,cost⟩ :=
    FinalDispatch.solve_bit adjacency costs encoded initial bounded pc0 dense empty table graph pairs
  exact ⟨k,charge,out,run,rep,tableOut,graphOut,pairsOut,ra,rb,rc,src,stack,pc,next,ext,stop,
    cost.trans (physical_le_eval adjacency costs ds
      (by omega) (by omega) (by omega) (by omega) (by omega))⟩

end DirectedFlowCutGap.FinalDispatchEnvelope
