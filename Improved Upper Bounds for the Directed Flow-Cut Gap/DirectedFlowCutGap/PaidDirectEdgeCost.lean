import DirectedFlowCutGap.PaidEdgeRoundCost
import DirectedFlowCutGap.PaidVertexAmplificationCost
namespace DirectedFlowCutGap.PaidDirectEdgeWire

open BinaryArithmetic BinaryRational RawNonnegativeRational Polynomial
open EncodedEdgeLineInput EncodedVertexAmplification PhysicalSolverCostEnvelope
open PhysicalIntegerRoundingCost (eval_mono)
open PhysicalBinaryEdgeCost (roundPolynomial widthPolynomial)
open PhysicalAmplifiedBinaryEdge (lineWithCost line_value lineBudget line_paid)
open BinaryEdgeProjection (outputBudget)

private theorem scalar_list (xs : List Fraction) :
    (xs.map fun q => q.num.length+q.den.length+1).sum=LambdaRowProgram.rowBits xs+xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,LambdaRowProgram.rowBits,List.length_cons,ih]
    omega

private theorem row_fits {n b : ℕ} (D : Input n) (row : FractionalCoverRawCore.RawRow (lineSize n))
    (hw : ∀ i, (FractionalCoverRawCore.get row i).Bounded b)
    (hc : ∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ b ∧ D.costs[u.val][v.val].den.size ≤ b) :
    BinaryEdgeGadget.InputFits (roundingInput D row) b := by
  constructor
  · intro u v
    simpa only [roundingInput,Vector.getElem_ofFn] using hw (edgeIndex (u,v))
  · intro u v
    obtain ⟨a,c⟩ := hc u v
    exact ⟨(Nat.size_le.mp a).le,(Nat.size_le.mp c).le⟩

attribute [local irreducible] DirectBinaryEdgeWire.read lineWithCost BinaryFractionalGuesses.solveInput

set_option maxHeartbeats 2300000 in
theorem run_polynomial : ∃ p : Polynomial ℕ, ∀ {n B : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits), 1 ≤ B →
    (∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ B ∧ D.costs[u.val][v.val].den.size ≤ B) →
      (run κ D mode tape).2 ≤ p.eval (n+D.demands.length+B+κ) := by
  obtain ⟨q,hq⟩ := PaidVertexRounding.polynomial_bound
  obtain ⟨p,hp⟩ := PaidVertexAmplification.polynomial_on_rows (roundPolynomial q)
  let line : Polynomial ℕ := X*2+X^2
  let costs := line+X+line*(2*X)+1
  let sourceSize := 2*(costs+line*line+X*(line+line))+3*(line+line+X)+3
  let vertices := BinaryEdgeGadget.dimension (X : Polynomial ℕ)
  let exponent : Polynomial ℕ := (X+2)*X+1
  let pad := X+line+(costs+1)+sourceSize+vertices+exponent+drawPolynomial vertices
  let cap := 1+PhysicalSourceDispatch.instructionPolynomial
  let lookup := DirectBinaryEdgeWire.rowBudget X cap cap
  let prefixCost := BinaryFractionalWorkPolynomial.envelope+lookup
  refine ⟨(prefixCost+p).comp pad+lineBudget line X X+outputBudget X+BinarySolverOuterControls.budget X X,?_⟩
  intro n B κ D mode tape positive fits
  let y := n+D.demands.length+B+κ
  let x := pad.eval y
  let z := trialEnvelope.eval x+x
  let binary := (lineWithCost D).1
  let W := ChargedVertexModes.priceWidth binary
  let e := confidenceExponent n κ
  let draw := EncodedEdgeSolver.drawBound n
  let T := ChargedPhysicalVertexSolver.trialLimit (BinaryFractionalGuesses.decodeInput binary) draw e (e+1)
  let cover := BinaryFractionalGuesses.solveInput binary
  let reader := DirectBinaryEdgeWire.read cover.1
  have hn : n ≤ y := by dsimp only [y]; omega
  have hd : D.demands.length ≤ y := by dsimp only [y]; omega
  have hb : B ≤ y := by dsimp only [y]; omega
  have hk : κ ≤ y := by dsimp only [y]; omega
  have yx : y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
  have xz : x ≤ z := Nat.le_add_left _ _
  have hline : lineSize n ≤ line.eval y := by
    simp only [line,eval_add,eval_mul,eval_ofNat,eval_X,lineSize,pow_two]
    gcongr
  have hs : PhysicalEdgeSolver.lineInputSizeBound n D.demands.length B ≤ costs.eval y := by
    simp only [costs,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,PhysicalEdgeSolver.lineInputSizeBound]
    gcongr
  have hl : lineSize n ≤ x := by
    apply hline.trans
    simp only [x,pad,eval_add,eval_X]
    omega
  have store := PhysicalEdgeSolver.line_size_le D positive fits
  rw [← line_value D] at store
  change OriginalStoreInitial.inputSize binary.costs binary.demands ≤ _ at store
  have hW : W ≤ x := by
    have lim := store.trans hs
    unfold OriginalStoreInitial.inputSize at lim
    simp only [x,pad,eval_add,eval_one,W,ChargedVertexModes.priceWidth,eval_X]
    omega
  have he : e+1 ≤ x := by
    have h := Nat.add_le_add_right ((exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right hn 2) hk)) 1
    have next : exponent.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    simp only [exponent,eval_add,eval_mul,eval_ofNat,eval_X,eval_one] at next
    exact h.trans next
  have dim : BinaryEdgeGadget.dimension n ≤ vertices.eval y := by
    simp only [vertices,BinaryEdgeGadget.dimension,eval_add,eval_mul,eval_ofNat,eval_X]
    gcongr
  have vsize : BinaryEdgeGadget.dimension n ≤ z := by
    apply dim.trans
    simp only [x,z,pad,eval_add,eval_X]
    omega
  have draws : draw ≤ x := by
    have h : (drawPolynomial vertices).eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    rw [drawPolynomial_eval] at h
    apply le_trans ?_ h
    have hdim : 2*n*(Nat.log2 n+4) ≤ vertices.eval y :=
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log2_le_self _) 4)).trans dim
    unfold draw EncodedEdgeSolver.drawBound roundDrawBound EncodedUniformRounding.drawBound
    gcongr
  have source : (PhysicalSourceDispatch.input binary).length ≤ x := by
    have h : sourceSize.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    apply le_trans ?_ h
    change (PhysicalSourceDispatch.input (lineWithCost D).1).length ≤ _
    rw [line_value]
    apply (PhysicalSourceSizeBounds.line_source_size_le D positive fits).trans
    simp only [PhysicalSourceSizeBounds.lineSourceSizeBound,PhysicalSourceSizeBounds.sourceSizeBound,sourceSize,
      eval_add,eval_mul,eval_ofNat,eval_X]
    gcongr
  have eBound : e ≤ x := (Nat.le_succ _).trans he
  have good := ChargedVertexModes.priceWidth_bounds binary
  have trials : T ≤ z :=
    (trialLimit_le binary draw e (e+1) hl hW draws eBound he good).trans (Nat.le_add_right _ _)
  have plan : reader.1=PhysicalCoverReader.plan cover.1 := DirectBinaryEdgeWire.read_value _
  have planRows : ChargedPhysicalVertexSolver.rowsCount reader.1 ≤
      ChargedPhysicalVertexSolver.rowLimit (BinaryFractionalGuesses.decodeInput binary) := by
    rw [plan]
    exact ChargedPhysicalVertexSolver.rowsCount_le binary
  have rounds : ∀ rows, reader.1=.covers rows → ∀ row ∈ rows, ∀ bits,
      (round D mode T (EncodedVertexSolver.roundingInput (BinaryFractionalGuesses.decodeInput binary) row) bits).2
        ≤ (roundPolynomial q).eval z := by
    intro rows stored row mem bits
    rw [plan] at stored
    let b := widthPolynomial.eval z
    have bsize : b=z+1+PhysicalSourceDispatch.instructionPolynomial.eval z := by
      simp only [b,widthPolynomial,eval_add,eval_X,eval_one]
    have H := eval_mono PhysicalSourceDispatch.instructionPolynomial (source.trans xz)
    have orig : B ≤ z := (hb.trans yx).trans xz
    have field := PhysicalCoverWidthEnvelope.rows_width binary rows stored row mem
    have actual : BinaryEdgeGadget.InputFits (roundingInput D row) b :=
      row_fits D row (fun i => Code.bounded_mono (field i) (by omega))
        (fun u v => ⟨(fits u v).1.trans (by omega),(fits u v).2.trans (by omega)⟩)
    exact round_paid q hq D mode vsize ((hn.trans yx).trans xz) trials _ bits actual le_rfl
  have work := hp binary (round D mode) draw e (e+1) reader.1 cover.2 reader.2 tape
    hl hW draws eBound he (ChargedVertexModes.priceWidth_positive binary) good planRows rounds
  have ds : binary.demands.length ≤ x := by
    have count : binary.demands.length=D.demands.length := by
      simp only [binary,line_value,PhysicalEdgeSolver.binaryLineInput,lineInput,List.length_map]
    rw [count]
    exact hd.trans yx
  have scalar : BinaryFractionalGuessesBounds.scalarSize binary.costs ≤ x := by
    have lim := store.trans hs
    unfold BinaryFractionalGuessesBounds.scalarSize
    unfold OriginalStoreInitial.inputSize at lim
    rw [scalar_list,Vector.length_toList]
    simp only [x,pad,eval_add,eval_one,eval_X]
    omega
  have lp : cover.2 ≤ BinaryFractionalWorkPolynomial.envelope.eval x :=
    (BinaryFractionalGuessesBounds.solveInput_charge_from_data binary).trans (BinaryFractionalWorkPolynomial.bound hl ds scalar)
  have lookupCap : 1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input binary).length ≤ cap.eval x := by
    simp only [cap,eval_add,eval_one]
    exact Nat.add_le_add_left (eval_mono _ source) 1
  have readback : reader.2 ≤ lookup.eval x := by
    apply (DirectBinaryEdgeWire.read_solveInput_paid binary).trans
    simp only [lookup,DirectBinaryEdgeWire.rowBudget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X]
    gcongr
  have liftLine : lineBudget (lineSize n) D.demands.length B ≤ (lineBudget line X X).eval y := by
    simp only [lineBudget,BinaryLineLabels.budget_eval,BinaryLineLabels.demandBudget_eval,
      BinaryLineLabels.assemblyBudget_eval,eval_add,eval_mul,eval_ofNat,eval_X,eval_pow]
    unfold BinaryLineLabels.budget BinaryLineLabels.demandBudget BinaryLineLabels.assemblyBudget
    gcongr
  have liftOutput : outputBudget n ≤ (outputBudget (X : Polynomial ℕ)).eval y := by
    simp only [outputBudget,BinaryEdgeProjection.readbackBudget,BinaryLineLabels.budget_eval,
      eval_add,eval_mul,eval_ofNat,eval_X,eval_pow]
    unfold BinaryLineLabels.budget
    gcongr
  have setup := (line_paid D positive fits).trans liftLine
  have meter := (BinarySolverOuterControls.edge_paid n κ).trans (BinarySolverOuterControls.budget_mono hn hk)
  have total := phase_paid κ D mode tape
  dsimp only at total
  rw [BinarySolverOuterControls.edge_draws,BinarySolverOuterControls.edge_extra,BinarySolverOuterControls.edge_confidence] at total
  apply total.trans
  simp only [eval_add,eval_comp,BinarySolverOuterControls.budget_eval,eval_X,prefixCost]
  change (lineWithCost D).2+(BinarySolverOuterControls.edge n κ).paid+cover.2+reader.2+
    (PaidVertexAmplification.runWithPlan binary (round D mode) draw e (e+1) reader.1 cover.2 reader.2 tape).2+
      outputBudget n ≤ BinaryFractionalWorkPolynomial.envelope.eval x+lookup.eval x+p.eval x+
        (lineBudget line X X).eval y+(outputBudget (X : Polynomial ℕ)).eval y+BinarySolverOuterControls.budget y y
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add setup meter) lp)
    readback) work) liftOutput).trans_eq (by ac_rfl)

end DirectedFlowCutGap.PaidDirectEdgeWire
