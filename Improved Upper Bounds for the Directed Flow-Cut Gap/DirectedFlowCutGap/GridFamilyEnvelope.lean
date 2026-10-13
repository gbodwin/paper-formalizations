import DirectedFlowCutGap.ActualGridFamilyInput
import DirectedFlowCutGap.SourcePackingPolynomialCosts

noncomputable section


/-! Bounds on the words actually constructed by the original-input prefix.
No loop range or short encoding is assumed of a supplied exponent. -/
namespace DirectedFlowCutGap.GridFamilyEnvelope
open BinaryArithmetic BinaryRational

theorem row_bits (rows : List Fraction) :
    InputWidthProgram.bits rows=LambdaRowProgram.rowBits rows := by
  induction rows with
  | nil => rfl
  | cons q qs ih =>
    change q.num.length+q.den.length+InputWidthProgram.bits qs=
      q.num.length+q.den.length+LambdaRowProgram.rowBits qs
    rw [ih]

def wordBound (n S : ℕ) : ℕ := 3*S+3*n+20

theorem fuel_length (rows : List Fraction) :
    (GridFamilyInput.fuel rows).length ≤ wordBound rows.length (LambdaRowProgram.rowBits rows) := by
  let dim := GridInputProgram.dimension rows
  let wid := GridInputProgram.width rows
  let sz := (BinaryCounters.sizeBits dim).1
  let tw := (mulCanonical [false,true] wid).1
  let tn := (mulCanonical [false,true] sz).1
  let sum := (addCanonical tw tn).1
  have hd : dim.length ≤ rows.length := GridInputProgram.dimension_length rows
  have hw : wid.length ≤ LambdaRowProgram.rowBits rows := by
    simpa only [wid,GridInputProgram.width,row_bits] using InputWidthProgram.width_length rows
  have hs : sz.length ≤ dim.length := FractionWidthProgram.size_length dim
  have htw := GridFuelProgram.canonical_mul_length [false,true] wid
  have htn := GridFuelProgram.canonical_mul_length [false,true] sz
  have hsum := GridFuelProgram.canonical_add_length tw tn
  have hout := GridFuelProgram.canonical_add_length sum [true,true]
  simp only [List.length_cons,List.length_nil] at htw htn hout
  change tw.length ≤ 2*2+wid.length+1 at htw
  change tn.length ≤ 2*2+sz.length+1 at htn
  change sum.length ≤ tw.length+tn.length+1 at hsum
  change (GridFamilyInput.fuel rows).length ≤ sum.length+2+1 at hout
  unfold wordBound
  omega

theorem fuel_value (rows : List Fraction) :
    value (GridFamilyInput.fuel rows)=LambdaGridProgram.gridLimit rows := rfl

theorem initial_range (rows : List Fraction) :
    value ([] : Bits)+value (GridFamilyInput.fuel rows) ≤ LambdaGridProgram.gridLimit rows ∧
    ([] : Bits).length+value (GridFamilyInput.fuel rows) ≤
      wordBound rows.length (LambdaRowProgram.rowBits rows) := by
  have h := LambdaGridProgram.gridLimit_bound rows
  simp only [value,List.length_nil,Nat.zero_add,fuel_value]
  unfold wordBound
  omega

/-- Both invariants are preserved by the literal increment/predecessor calls. -/
theorem advance_range (exponent fuel : Bits) (L W : ℕ)
    (positive : 0<value fuel) (range : value exponent+value fuel ≤ L)
    (lengths : exponent.length+value fuel ≤ W) :
    value (increment true exponent).1+value (predecessor fuel).1 ≤ L ∧
    (increment true exponent).1.length+value (predecessor fuel).1 ≤ W ∧
    (predecessor fuel).1.length ≤ W := by
  have hi := increment_spec true exponent
  have hp := predecessor_spec fuel
  have hs : Nat.size (value fuel-1) ≤ value fuel-1 := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [Bool.toNat_true] at hi
  omega
end DirectedFlowCutGap.GridFamilyEnvelope


namespace DirectedFlowCutGap.GridFamilyEnvelope
open BinaryArithmetic BinaryRational

/-- Nonrecursive numerical prefix envelope in row count and stored cost bits. -/
def prefixBound (n S : ℕ) : ℕ :=
  (160*(S+1)^2+32)*n+4+(8*n+12)*n+900*(n+S+15)^2+30

def minimumBound (n S : ℕ) : ℕ :=
  RowVertices.instructionBound n+(4*S+(6400*(S+1)^2+36)*n+16)+8

/-- Uniform bound for one guess, with the existing polynomial packing bound.
The exponent occurs only through the proved word-length bound W. -/
def guessBound (d n S W : ℕ) : ℕ :=
  minimumBound n S+
    (prefixBound n S+50100*(3*S+5*n+W+8)^2+12+
      ScalarAdditionRow.instructionBound n (S+2*(3*S+3*n+7))+8)+8+
    EnumeratedPacking.instructionBound d n (S+(3*S+3*n+7)+2)+12

theorem prefix_exact (rows : List Fraction) :
    GridInputProgram.inputSteps rows=prefixBound rows.length (LambdaRowProgram.rowBits rows) := by
  simp only [GridInputProgram.inputSteps,InputWidthProgram.inputSteps,row_bits,prefixBound]

theorem minimum_exact (rows : List Fraction) :
    OriginalRowMinimum.inputSteps rows=minimumBound rows.length (LambdaRowProgram.rowBits rows) := by
  change RowVertices.instructionBound rows.length+
    (4*InputWidthProgram.bits rows+(6400*(InputWidthProgram.bits rows+1)^2+36)*rows.length+16)+8=_
  rw [row_bits]
  rfl

theorem guess_bound (d : ℕ) (rows : List Fraction) (exponent : Bits) (W : ℕ)
    (range : value exponent ≤ LambdaGridProgram.gridLimit rows) (width : exponent.length ≤ W) :
    MinimumGuess.inputSteps d rows exponent ≤ guessBound d rows.length (LambdaRowProgram.rowBits rows) W := by
  apply (MinimumGuess.inputSteps_le_grid d rows exponent range).trans
  unfold MinimumGuess.gridInputSteps MinimumShift.gridInputSteps ShiftedGridProgram.gridInputSteps
    LambdaGridProgram.gridInputSteps MinimumGuess.gridShiftedWidth guessBound
  simp only [List.length_replicate,prefix_exact,minimum_exact]
  have h : 3*LambdaRowProgram.rowBits rows+4*rows.length+rows.length+exponent.length+8 ≤
      3*LambdaRowProgram.rowBits rows+5*rows.length+W+8 := by omega
  have hp := Nat.mul_le_mul_left 50100 (Nat.pow_le_pow_left h 2)
  omega

/-- One whole iteration, including zero test, increment, predecessor and call overhead. -/
def bodyBound (d n S W : ℕ) : ℕ := guessBound d n S W+36*W+105
end DirectedFlowCutGap.GridFamilyEnvelope


namespace DirectedFlowCutGap.GridFamilyEnvelope
open BinaryArithmetic BinaryRational

/-- The recursive controller envelope is discharged from conserved numeric fuel
and increasing exponent invariants. Padded fuel is allowed and explicitly paid. -/
theorem loop_bound (d : ℕ) (rows : List Fraction) (exponent fuel : Bits) (W : ℕ)
    (range : value exponent+value fuel ≤ LambdaGridProgram.gridLimit rows)
    (lengths : exponent.length+value fuel ≤ W) (fuelLength : fuel.length ≤ W) :
    GridFamily.instructionBound d rows exponent fuel ≤
      (value fuel+1)*bodyBound d rows.length (LambdaRowProgram.rowBits rows) W := by
  revert range lengths fuelLength
  induction exponent, fuel using GridFamily.instructionBound.induct with
  | case1 exponent fuel hz =>
    intro range lengths fuelLength
    have z := (isZero_spec fuel).1.mp hz
    have h := BinaryZeroProgram.steps_bound fuel
    rw [GridFamily.instructionBound]
    simp only [dite_eq_left hz,z,Nat.zero_add,Nat.one_mul]
    unfold bodyBound
    omega
  | case2 exponent fuel hz ih =>
    intro range lengths fuelLength
    have positive : 0<value fuel := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec fuel).1.mpr h))
    have next := advance_range exponent fuel (LambdaGridProgram.gridLimit rows) W positive range lengths
    have tail := ih next.1 next.2.1 next.2.2
    have guess := guess_bound d rows exponent W (by omega) (by omega)
    have zero := BinaryZeroProgram.steps_bound fuel
    have inc := BinaryIncrementProgram.steps_bound exponent
    have pred := BinaryPredecessorProgram.steps_bound fuel
    unfold BinaryPredecessorProgram.inputSteps at pred
    have pv := (predecessor_spec fuel).1
    have count : value (predecessor fuel).1+1=value fuel := by omega
    rw [count] at tail
    rw [GridFamily.instructionBound]
    simp only [dite_eq_right hz]
    rw [Nat.add_mul,Nat.one_mul]
    unfold bodyBound at *
    omega

/-- A numerical envelope using only original demand count, row count and stored bits. -/
def instructionBound (d n S : ℕ) : ℕ :=
  prefixBound n S+(2*S+2*n+4)*bodyBound d n S (wordBound n S)+16

theorem original_input_bound (d : ℕ) (rows : List Fraction) :
    GridFamilyInput.inputSteps d rows ≤ instructionBound d rows.length (LambdaRowProgram.rowBits rows) := by
  have r := initial_range rows
  have b := loop_bound d rows [] (GridFamilyInput.fuel rows)
    (wordBound rows.length (LambdaRowProgram.rowBits rows)) r.1 r.2 (fuel_length rows)
  have lim := LambdaGridProgram.gridLimit_bound rows
  have n : value (GridFamilyInput.fuel rows)+1 ≤ 2*LambdaRowProgram.rowBits rows+2*rows.length+4 := by
    rw [fuel_value]
    omega
  have mult := Nat.mul_le_mul_right
    (bodyBound d rows.length (LambdaRowProgram.rowBits rows)
      (wordBound rows.length (LambdaRowProgram.rowBits rows))) n
  unfold GridFamilyInput.inputSteps instructionBound
  rw [prefix_exact]
  omega
end DirectedFlowCutGap.GridFamilyEnvelope


namespace DirectedFlowCutGap.GridFamilyEnvelope
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

/-- The same original-root physical run receives a nonrecursive input-only bound.
The initial representation, store/address bounds and dense cursor remain explicit. -/
theorem family_polynomial_bit {n H B : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    (initial : BitState 10760) (bounded : initial.Bounded H B) (pc0 : initial.pc=10758)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a
      (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.b
      (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList (eraseState initial).heap (eraseState initial).registers.c xs) :
    ∃ k charge out,Run GridFamilyInput.program k charge initial [] out ∧
      GridFamily.StateList (eraseState out).heap (eraseState out).registers.d
        (GridFamily.values adjacency ds costs [] (GridFamilyInput.fuel costs.toList)) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a
        (IndexedRationalRead.fields costs.toList) ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState initial).registers.b
        (GraphRelaxationRefinement.matrix adjacency) ∧
      DemandCollection.DemandList (eraseState out).heap (eraseState initial).registers.c xs ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=10759 ∧ value out.next=out.heap.length ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt GridFamilyInput.program out).result=none ∧
      charge+(attempt GridFamilyInput.program out).operations ≤ completeBound 10760 H B
        (instructionBound ds.length costs.toList.length (LambdaRowProgram.rowBits costs.toList)) := by
  obtain ⟨k,charge,out,run,rep,tableOut,graphOut,pairsOut,src,stack,pc,next,ext,stop,cost⟩ :=
    GridFamilyInput.family_bit adjacency costs encoded initial bounded pc0 dense empty table graph pairs
  exact ⟨k,charge,out,run,rep,tableOut,graphOut,pairsOut,src,stack,pc,next,ext,stop,
    cost.trans (SupportSearchEncoding.complete_mono 10760 H B _ _
      (original_input_bound ds.length costs.toList))⟩
end DirectedFlowCutGap.GridFamilyEnvelope


/-! A fixed polynomial majorant, in a common bound on original demand count,
row count, stored cost bits, initial heap size and address/source width. -/
namespace DirectedFlowCutGap.GridFamilyEnvelope
open Polynomial ImmutableReferenceSimulation ImmutableReferenceTerminal SourcePackingPolynomial

def prefixPolynomial : Polynomial ℕ :=
  (160*(X+1)^2+32)*X+4+(8*X+12)*X+900*(X+X+15)^2+30

def minimumPolynomial : Polynomial ℕ :=
  (8*X+19)*X+10+(4*X+(6400*(X+1)^2+36)*X+16)+8

def wordPolynomial : Polynomial ℕ := 3*X+3*X+20

def guessPolynomial : Polynomial ℕ :=
  minimumPolynomial+
    (prefixPolynomial+50100*(3*X+5*X+wordPolynomial+8)^2+12+
      (X*(20000*(2*(X+2*(3*X+3*X+7))+2)^2+11)+4)+8)+8+
    poly_EnumeratedPacking_instructionBound X X (X+(3*X+3*X+7)+2)+12

def instructionPolynomial : Polynomial ℕ :=
  prefixPolynomial+(2*X+2*X+4)*(guessPolynomial+36*wordPolynomial+105)+16

theorem instruction_mono {d d' n n' S S' : ℕ}
    (hd : d≤d') (hn : n≤n') (hs : S≤S') :
    instructionBound d n S ≤ instructionBound d' n' S' := by
  unfold instructionBound bodyBound guessBound minimumBound wordBound prefixBound
    RowVertices.instructionBound ScalarAdditionRow.instructionBound
  gcongr

theorem instruction_diagonal_le_eval (N : ℕ) :
    instructionBound N N N ≤ instructionPolynomial.eval N := by
  have solver := bound_EnumeratedPacking_instructionBound N
    (d:=N) (n:=N) (B:=N+(3*N+3*N+7)+2)
    (p_d:=X) (p_n:=X) (p_B:=X+(3*X+3*X+7)+2)
    (by simp) (by simp) (by simp)
  unfold instructionPolynomial guessPolynomial prefixPolynomial minimumPolynomial wordPolynomial
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  unfold instructionBound bodyBound guessBound minimumBound wordBound prefixBound
    RowVertices.instructionBound ScalarAdditionRow.instructionBound
  gcongr

theorem instruction_le_eval {d n S N : ℕ} (hd : d≤N) (hn : n≤N) (hs : S≤N) :
    instructionBound d n S ≤ instructionPolynomial.eval N :=
  (instruction_mono hd hn hs).trans (instruction_diagonal_le_eval N)

/-- A single fixed polynomial also pays for the actual reference interpreter's
successful prefix, copies, heap lookups and final terminal attempt. -/
def physicalPolynomial : Polynomial ℕ :=
  C (controlCost 10760+128)*instructionPolynomial*(X+X+2*instructionPolynomial+1)^2+
    C (controlCost 10760+128)*(X+instructionPolynomial+1)*(X+instructionPolynomial+1)

theorem physical_eval (N : ℕ) :
    physicalPolynomial.eval N=completeBound 10760 N N (instructionPolynomial.eval N) := by
  simp only [physicalPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,
    completeBound,runBound,stepBound]

theorem physical_le_eval {d n S H B N : ℕ}
    (hd : d≤N) (hn : n≤N) (hs : S≤N) (hh : H≤N) (hb : B≤N) :
    completeBound 10760 H B (instructionBound d n S) ≤ physicalPolynomial.eval N := by
  rw [physical_eval]
  have bound := instruction_le_eval hd hn hs
  unfold completeBound runBound stepBound
  gcongr

theorem fixed_polynomial_bound : ∃ p : Polynomial ℕ, ∀ d n S H B N : ℕ,
    d≤N → n≤N → S≤N → H≤N → B≤N →
      completeBound 10760 H B (instructionBound d n S) ≤ p.eval N :=
  ⟨physicalPolynomial,fun _ _ _ _ _ _ hd hn hs hh hb => physical_le_eval hd hn hs hh hb⟩
end DirectedFlowCutGap.GridFamilyEnvelope


namespace DirectedFlowCutGap.GridFamilyEnvelope
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

/-- One fixed polynomial bounds the same run from the three original roots.
This measures an already represented input; the full dispatcher remains separate. -/
theorem family_fixed_polynomial_bit {n H B : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    (initial : BitState 10760) (bounded : initial.Bounded H B) (pc0 : initial.pc=10758)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a
      (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.b
      (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList (eraseState initial).heap (eraseState initial).registers.c xs) :
    ∃ k charge out,Run GridFamilyInput.program k charge initial [] out ∧
      GridFamily.StateList (eraseState out).heap (eraseState out).registers.d
        (GridFamily.values adjacency ds costs [] (GridFamilyInput.fuel costs.toList)) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a
        (IndexedRationalRead.fields costs.toList) ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState initial).registers.b
        (GraphRelaxationRefinement.matrix adjacency) ∧
      DemandCollection.DemandList (eraseState out).heap (eraseState initial).registers.c xs ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=10759 ∧ value out.next=out.heap.length ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt GridFamilyInput.program out).result=none ∧
      charge+(attempt GridFamilyInput.program out).operations ≤ physicalPolynomial.eval
        (ds.length+costs.toList.length+LambdaRowProgram.rowBits costs.toList+H+B+1) := by
  obtain ⟨k,charge,out,run,rep,tableOut,graphOut,pairsOut,src,stack,pc,next,ext,stop,cost⟩ :=
    family_polynomial_bit adjacency costs encoded initial bounded pc0 dense empty table graph pairs
  exact ⟨k,charge,out,run,rep,tableOut,graphOut,pairsOut,src,stack,pc,next,ext,stop,
    cost.trans (physical_le_eval (by omega) (by omega) (by omega) (by omega) (by omega))⟩
end DirectedFlowCutGap.GridFamilyEnvelope
