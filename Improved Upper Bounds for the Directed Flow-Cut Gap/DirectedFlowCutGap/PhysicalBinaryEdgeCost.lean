import DirectedFlowCutGap.PhysicalAmplifiedBinaryEdge

/-! Apply the binary gadget and rounding bounds to the line cover rows
that the physical dispatcher actually returns. -/

namespace DirectedFlowCutGap.PhysicalBinaryEdgeCost

open BinaryArithmetic BinaryRational RawNonnegativeRational Polynomial
open EncodedVertexAmplification EncodedEdgeLineInput PhysicalSolverCostEnvelope
open PhysicalIntegerRoundingCost (eval_mono)
open PhysicalAmplifiedBinaryEdge
open PhysicalAmplifiedEdgeSolver (EdgeResult)
open PhysicalAmplifiedBinaryVertex (arithmeticPolynomial)

noncomputable def widthPolynomial : Polynomial ℕ := X+1+PhysicalSourceDispatch.instructionPolynomial

noncomputable def roundPad : Polynomial ℕ := X+X^2*(widthPolynomial+1)+X+1

noncomputable def roundPolynomial (q : Polynomial ℕ) : Polynomial ℕ :=
  (q+arithmeticPolynomial).comp roundPad+BinaryEdgeGadget.budget X widthPolynomial+
    pullbackBudget X (BinaryEdgeGadget.dimension X)+64*(X+4)^2*(X+1)^2

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

set_option maxHeartbeats 1500000 in
theorem round_paid (q : Polynomial ℕ)
    (qBound : ∀ n T x, n ≤ x → T ≤ x →
      (∀ (D : EncodedUnitCostReplication.Input n) tape (r : PhysicalIntegerRounding.Result n),
        PhysicalVertexRounding.weighted T D tape=some r → r.paid ≤ q.eval x) ∧
      (∀ (D : EncodedUnitCostReplication.Input n) tape (r : PhysicalIntegerRounding.Result n),
        PhysicalVertexRounding.size T D tape=some r → r.paid ≤ q.eval x))
    {n b T z : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode)
    (dimensions : BinaryEdgeGadget.dimension n ≤ z) (hn : n ≤ z) (trials : T ≤ z)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits)
    (fits : BinaryEdgeGadget.InputFits (roundingInput D r.weights) b) (width : b ≤ widthPolynomial.eval z)
    {out : PhysicalIntegerRounding.Result (lineSize n)} (ran : round D mode T r tape=some out) :
    out.paid ≤ (roundPolynomial q).eval z := by
  let p := BinaryEdgeGadget.build (roundingInput D r.weights)
  let g := p.1
  let y := roundPad.eval z
  let w := widthPolynomial.eval z
  change ((PhysicalAmplifiedBinaryVertex.runner mode T g.data tape).map
    (PhysicalVertexRounding.project
      (fun cut => (toLine (EncodedEdgeRounding.pullback g cut),pullbackBudget n g.size))
      (p.2+64*(n+4)^2*(n+1)^2)))=some out at ran
  obtain ⟨inner,call,rfl⟩ := Option.map_eq_some_iff.mp ran
  have dim : g.size ≤ z := (BinaryEdgeGadget.size_le _).trans dimensions
  have hy : y=z+z^2*(w+1)+z+1 := by
    simp only [y,roundPad,w,eval_add,eval_X,eval_pow,eval_mul,eval_one]
  have more : z ≤ y := by omega
  have fields := BinaryEdgeGadget.fields_fit (roundingInput D r.weights) fits
  have k : n^2*(b+1) ≤ z^2*(w+1) := by gcongr
  have bytes : n^2*(b+1)+n+1 ≤ y+1+PhysicalSourceDispatch.instructionPolynomial.eval y := by omega
  have innerPaid := PhysicalAmplifiedBinaryVertex.runner_paid q qBound mode _ tape fields
    (dim.trans more) (trials.trans more) bytes call
  have gadget : p.2 ≤ BinaryEdgeGadget.budget z w :=
    (BinaryEdgeGadget.build_paid _ fits).trans (BinaryEdgeGadget.budget_mono hn width)
  have project : 64*(n+4)^2*(n+1)^2 ≤ 64*(z+4)^2*(z+1)^2 := by gcongr
  have pull : pullbackBudget n g.size ≤ pullbackBudget z (BinaryEdgeGadget.dimension z) := by
    have larger : g.size ≤ BinaryEdgeGadget.dimension z := by
      apply (BinaryEdgeGadget.size_le (roundingInput D r.weights)).trans
      unfold BinaryEdgeGadget.dimension
      gcongr
    unfold pullbackBudget
    gcongr
  simp only [roundPolynomial,pullbackBudget,BinaryEdgeGadget.dimension,eval_add,eval_comp,eval_X,eval_ofNat,
    eval_one,eval_mul,eval_pow,BinaryEdgeGadget.budget_eval]
  change p.2+64*(n+4)^2*(n+1)^2+inner.paid+pullbackBudget n g.size ≤
    (q.eval y+arithmeticPolynomial.eval y)+BinaryEdgeGadget.budget z w+
      (pullbackBudget z (BinaryEdgeGadget.dimension z))+64*(z+4)^2*(z+1)^2
  rw [eval_add] at innerPaid
  omega

set_option maxHeartbeats 1900000 in
theorem edge_polynomial : ∃ p : Polynomial ℕ, ∀ {n B : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits), 1 ≤ B →
    (∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ B ∧ D.costs[u.val][v.val].den.size ≤ B) →
    ∀ {out : EdgeResult n}, run κ D mode tape=some out →
      out.dispatch+out.readback+out.roundingAndSelection ≤ p.eval (n+D.demands.length+B+κ) := by
  obtain ⟨q,hq⟩ := PhysicalVertexRoundingCost.polynomial_bound
  obtain ⟨p,hp⟩ := run_polynomial_on_rows (roundPolynomial q)
  let line : Polynomial ℕ := X*2+X^2
  let costs := line+X+line*(2*X)+1
  let sourceSize := 2*(costs+line*line+X*(line+line))+3*(line+line+X)+3
  let vertices := BinaryEdgeGadget.dimension (X : Polynomial ℕ)
  let exponent : Polynomial ℕ := (X+2)*X+1
  let pad := X+line+(costs+1)+sourceSize+vertices+exponent+drawPolynomial vertices
  refine ⟨p.comp pad+lineBudget line X X+outputBudget X+BinarySolverOuterControls.budget X X,?_⟩
  intro n B κ D mode tape positive fits out ran
  let y := n+D.demands.length+B+κ
  let x := pad.eval y
  let z := trialEnvelope.eval x+x
  let binary := (lineWithCost D).1
  let W := ChargedVertexModes.priceWidth binary
  let e := confidenceExponent n κ
  let draw := EncodedEdgeSolver.drawBound n
  let T := ChargedPhysicalVertexSolver.trialLimit (BinaryFractionalGuesses.decodeInput binary) draw e (e+1)
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
  have hW : W ≤ x := by
    have store := PhysicalEdgeSolver.line_size_le D positive fits
    rw [← line_value D] at store
    change OriginalStoreInitial.inputSize binary.costs binary.demands ≤ _ at store
    unfold OriginalStoreInitial.inputSize at store
    have lim := store.trans hs
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
  rw [run_controls] at ran
  change ((PhysicalAmplifiedVertexSolver.run binary (round D mode) draw e (e+1) tape).map
    (finish D ((lineWithCost D).2+(BinarySolverOuterControls.edge n κ).paid)))=some out at ran
  obtain ⟨r,hr,rfl⟩ := Option.map_eq_some_iff.mp ran
  have rounds : ∀ rows, PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput binary).1=.covers rows →
      ∀ row ∈ rows, ∀ bits a, round D mode T
        (EncodedVertexSolver.roundingInput (BinaryFractionalGuesses.decodeInput binary) row) bits=some a →
        a.paid ≤ (roundPolynomial q).eval z := by
    intro rows stored row mem bits a called
    let b := widthPolynomial.eval z
    have bsize : b=z+1+PhysicalSourceDispatch.instructionPolynomial.eval z := by
      simp only [b,widthPolynomial,eval_add,eval_X,eval_one]
    have H := eval_mono PhysicalSourceDispatch.instructionPolynomial (source.trans xz)
    have orig : B ≤ z := (hb.trans yx).trans xz
    have fields := PhysicalCoverWidthEnvelope.rows_width binary rows stored row mem
    have actual : BinaryEdgeGadget.InputFits (roundingInput D row) b :=
      row_fits D row (fun i => Code.bounded_mono (fields i) (by omega))
        (fun u v => ⟨(fits u v).1.trans (by omega),(fits u v).2.trans (by omega)⟩)
    exact round_paid q hq D mode vsize ((hn.trans yx).trans xz) trials _ bits actual le_rfl called
  have work := hp binary (round D mode) draw e (e+1) tape hl hW draws eBound he source
    (ChargedVertexModes.priceWidth_positive binary) good rounds hr
  have setup := line_paid D positive fits
  have liftLine : lineBudget (lineSize n) D.demands.length B ≤ (lineBudget line X X).eval y := by
    simp only [lineBudget,lineAllowance,BinaryLineLabels.budget_eval,BinaryLineLabels.demandBudget_eval,eval_add,eval_mul,eval_ofNat,eval_X,eval_pow,eval_one]
    unfold BinaryLineLabels.budget BinaryLineLabels.demandBudget
    gcongr
  have liftOutput : outputBudget n ≤ (outputBudget (X : Polynomial ℕ)).eval y := by
    simp only [outputBudget,eval_add,eval_mul,eval_ofNat,eval_X,eval_pow,eval_one]
    gcongr
  have totalLine := setup.trans liftLine
  have meter := (BinarySolverOuterControls.edge_paid n κ).trans (BinarySolverOuterControls.budget_mono hn hk)
  simp only [finish,eval_add,eval_comp,BinarySolverOuterControls.budget_eval,eval_X]
  change r.dispatch+r.readback+
      (r.roundingAndSelection+((lineWithCost D).2+(BinarySolverOuterControls.edge n κ).paid)+outputBudget n) ≤
    p.eval x+(lineBudget line X X).eval y+(outputBudget (X : Polynomial ℕ)).eval y+BinarySolverOuterControls.budget y y
  omega

end DirectedFlowCutGap.PhysicalBinaryEdgeCost
