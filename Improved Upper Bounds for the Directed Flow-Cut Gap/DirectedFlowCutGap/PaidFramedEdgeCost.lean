import DirectedFlowCutGap.PaidDirectEdgeCost
namespace DirectedFlowCutGap.PaidDirectEdgeWire

open BinaryArithmetic BinaryRational Polynomial EncodedEdgeLineInput
open PhysicalCoverAccess (Read)
open PhysicalIntegerRoundingCost (eval_mono)

private theorem stored_member {n : ℕ} (D : EncodedEdgeInput.Input n) (i : Fin (n*n)) :
    BinaryFractionalRows.get D.costs i ∈ D.costs.toList := by
  change D.costs[i.val] ∈ D.costs.toList
  have hi : i.val < D.costs.toList.length := by simp only [Vector.length_toList,i.isLt]
  simpa only [Vector.getElem_toList] using List.getElem_mem hi

private theorem decoded_widths {n width : ℕ} (D : EncodedEdgeInput.Input n)
    (fields : ∀ q ∈ D.costs.toList, StoredBounded q width) (u v : Fin n) :
    let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
    raw.costs[u.val][v.val].num.size ≤ width+1 ∧ raw.costs[u.val][v.val].den.size ≤ width+1 := by
  let i := finProdFinEquiv (u,v)
  let a := BinaryFractionalRows.get D.costs i
  obtain ⟨hn,hd⟩ := fields a (stored_member D i)
  simp only [PhysicalBinaryEdgeWire.decode_value,EncodedEdgeInput.decodeInput,Vector.getElem_ofFn,
    BinaryFractionalRows.decode_get]
  change (value a.num).size ≤ _ ∧ (value a.den).size ≤ _
  exact ⟨((Nat.size_le.mpr (value_lt a.num)).trans hn).trans (Nat.le_succ _),
    ((Nat.size_le.mpr (value_lt a.den)).trans hd).trans (Nat.le_succ _)⟩

/-- The recorded work is polynomial in original source length and the
numerical confidence degree, for malformed input, short tapes and success. -/
theorem wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
    (edgeWithCost κ mode source tape).2 ≤ p.eval (source.length+κ) := by
  obtain ⟨q,paid⟩ := run_polynomial
  let pad : Polynomial ℕ := 3*X+1
  let decoding := PhysicalBinaryEdgeWire.decodeBudget (X : Polynomial ℕ) X
  refine ⟨PhysicalSourceInputJoin.parsePolynomial+(decoding+q.comp pad),?_⟩
  intro κ mode source tape
  let x := source.length+κ
  have xs : source.length ≤ x := Nat.le_add_right _ _
  have parse := ((PhysicalSourceInputJoin.edge_paid source).trans_eq
    (PhysicalSourceInputJoin.parsePolynomial_eval _).symm).trans (eval_mono _ xs)
  simp only [eval_add,eval_comp]
  unfold edgeWithCost
  apply Read.bind_bound parse
  rintro ⟨n,D⟩ stored
  have found : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ := by
    rwa [ChargedSourceAssembly.edge_value,← PhysicalSourceInputJoin.edge_value]
  obtain ⟨dim,demands,fields⟩ := ChargedSourceAssembly.edge_dimensions found
  let raw := PhysicalBinaryEdgeWire.decodeWithCost D
  have original (i : Fin (n*n)) : StoredBounded (BinaryFractionalRows.get D.costs i) source.length :=
    fields _ (stored_member D i)
  have bound := decoded_widths D fields
  have cap : n+raw.1.demands.length+(source.length+1)+κ ≤ pad.eval x := by
    change n+D.demands.length+(source.length+1)+κ ≤ _
    simp only [pad,eval_add,eval_mul,eval_ofNat,eval_one,eval_X]
    omega
  have executed := (paid κ raw.1 mode tape (Nat.le_add_left ..) bound).trans (eval_mono q cap)
  have loads : raw.2 ≤ decoding.eval x := by
    have nx := dim.trans xs
    apply (PhysicalBinaryEdgeWire.decode_paid D original).trans
    simp only [decoding,PhysicalBinaryEdgeWire.decodeBudget,BinaryEdgeProjection.readbackBudget,
      eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X]
    gcongr
  change raw.2+(run κ raw.1 mode tape).2 ≤ _
  exact Nat.add_le_add loads executed

/-- The line phase is bounded before any tape-dependent rounding. A rejected
literal source never reaches that phase. -/
theorem wire_line_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      (edgeWithLineControl κ mode source tape).2 ≤ p.eval source.length := by
  let dimension : Polynomial ℕ := X*2+X*X
  let width : Polynomial ℕ := X+1
  refine ⟨PhysicalAmplifiedBinaryEdge.lineControlBudget dimension width,?_⟩
  intro κ mode source tape
  unfold edgeWithLineControl edgeWithBoundaryControl
  dsimp only
  cases read : (PhysicalSourceInputJoin.edge source).1 with
  | none => exact Nat.zero_le _
  | some input =>
    obtain ⟨n,D⟩ := input
    have original : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ := by
      simpa only [ChargedSourceAssembly.edge_value,← PhysicalSourceInputJoin.edge_value] using read
    obtain ⟨size,_,fields⟩ := ChargedSourceAssembly.edge_dimensions original
    change (runOnWithLineControl κ mode D tape).2 ≤ _
    rw [runOn_line_work]
    have line := PhysicalAmplifiedBinaryEdge.line_control_paid (PhysicalBinaryEdgeWire.decodeWithCost D).1
      (show 1 ≤ source.length+1 by omega) (decoded_widths D fields)
    refine line.trans ?_
    simp only [PhysicalAmplifiedBinaryEdge.lineControlBudget_eval,dimension,width,eval_add,eval_mul,eval_X,
      eval_ofNat,eval_one,lineSize]
    unfold PhysicalAmplifiedBinaryEdge.lineControlBudget BinaryLineLabels.controlBudget
      BinaryArrayBatch.childCeiling BinaryVectorAccess.budget
    dsimp only
    gcongr

theorem wire_work_with_line_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let result := edgeWithLineControl κ mode source tape
      result.1.2+result.2 ≤ p.eval (source.length+κ) := by
  obtain ⟨old,charged⟩ := wire_polynomial
  obtain ⟨line,measured⟩ := wire_line_polynomial
  refine ⟨old+line,fun κ mode source tape => ?_⟩
  simp only [eval_add,edgeWithLineControl_value]
  exact Nat.add_le_add (charged κ mode source tape)
    ((measured κ mode source tape).trans (eval_mono line (Nat.le_add_right ..)))

/-- The reached price decode, line preparation and final output use only
polynomial scalar work in the source size. The borrowed tape is not counted. -/
theorem wire_boundary_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      (edgeWithBoundaryControl κ mode source tape).2.total ≤ p.eval source.length := by
  obtain ⟨lineBudget,linePaid⟩ := wire_line_polynomial
  let priceBudget := PhysicalBinaryEdgeWire.decodeControlBudget (X : Polynomial ℕ) X
  let outputBudget := BinaryEdgeProjection.outputControlBudget (X : Polynomial ℕ)
  refine ⟨priceBudget+lineBudget+outputBudget,?_⟩
  intro κ mode source tape
  have line := linePaid κ mode source tape
  change (edgeWithBoundaryControl κ mode source tape).2.line ≤ _ at line
  unfold BoundaryWork.total
  simp only [eval_add]
  unfold edgeWithBoundaryControl at line ⊢
  dsimp only at line ⊢
  cases read : (PhysicalSourceInputJoin.edge source).1 with
  | none => exact Nat.zero_le _
  | some input =>
    obtain ⟨n,D⟩ := input
    have original : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ := by
      simpa only [ChargedSourceAssembly.edge_value,← PhysicalSourceInputJoin.edge_value] using read
    obtain ⟨dim,_,fields⟩ := ChargedSourceAssembly.edge_dimensions original
    let work := (runOnWithBoundaryControl κ mode D tape).2
    have store (i : Fin (n*n)) : StoredBounded (BinaryFractionalRows.get D.costs i) source.length :=
      fields _ (stored_member D i)
    have prices : work.prices ≤ priceBudget.eval source.length := by
      rw [show work.prices=(PhysicalBinaryEdgeWire.decodeWithControl D).2 from runOn_prices_work κ mode D tape]
      apply (PhysicalBinaryEdgeWire.decode_control_paid D store).trans
      simp only [priceBudget,PhysicalBinaryEdgeWire.decodeControlBudget_eval,eval_X]
      unfold PhysicalBinaryEdgeWire.decodeControlBudget BinaryEdgeProjection.gridControlBudget
        BinaryArrayBatch.childCeiling BinaryVectorAccess.budget
      dsimp only
      gcongr
    have output : work.output ≤ outputBudget.eval source.length := by
      apply (runOn_output_paid κ mode D tape).trans
      simp only [outputBudget,BinaryEdgeProjection.outputControlBudget_eval,eval_X]
      unfold BinaryEdgeProjection.outputControlBudget BinaryEdgeProjection.gridControlBudget
        BinaryLineLabels.labelControlBudget BinaryArrayBatch.childCeiling BinaryVectorAccess.budget
      dsimp only
      gcongr
    rw [read] at line
    change work.line ≤ _ at line
    change work.prices+work.line+work.output ≤ _
    exact Nat.add_le_add (Nat.add_le_add prices line) output

theorem wire_work_with_boundary_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let result := edgeWithBoundaryControl κ mode source tape
      result.1.2+result.2.total ≤ p.eval (source.length+κ) := by
  obtain ⟨old,charged⟩ := wire_polynomial
  obtain ⟨boundary,measured⟩ := wire_boundary_polynomial
  refine ⟨old+boundary,fun κ mode source tape => ?_⟩
  simp only [eval_add,edgeWithBoundaryControl_value]
  exact Nat.add_le_add (charged κ mode source tape)
    ((measured κ mode source tape).trans (eval_mono boundary (Nat.le_add_right ..)))

private theorem roundControlBudget_eval (n : Polynomial ℕ) (x : ℕ) :
    (roundControlBudget n).eval x=roundControlBudget (n.eval x) := by
  simp only [roundControlBudget,BinaryEdgeProjection.gridControlBudget_eval,
    BinaryEdgeProjection.pullbackControlBudget_eval,BinaryEdgeGadget.dimension,BinaryVectorAccess.budget,
    eval_ofNat,eval_mul,eval_add,eval_pow,eval_one]

private theorem roundControlBudget_mono {n m : ℕ} (h : n ≤ m) : roundControlBudget n ≤ roundControlBudget m := by
  unfold roundControlBudget
  apply Nat.add_le_add
  · unfold BinaryEdgeProjection.gridControlBudget BinaryArrayBatch.childCeiling BinaryVectorAccess.budget
    dsimp only
    gcongr
  · exact BinaryEdgeProjection.pullbackControlBudget_mono h (by unfold BinaryEdgeGadget.dimension; gcongr)

/-- The additional work covers each reached fractional-row and cut projection
in every requested sample, including rounds that run out of tape. -/
theorem run_round_work_bound : ∃ p : Polynomial ℕ, ∀ {n B : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits), 1 ≤ B →
    (∀ u v : Fin n, D.costs[u.val][v.val].num.size ≤ B ∧ D.costs[u.val][v.val].den.size ≤ B) →
      (runWithRoundWork κ D mode tape).2 ≤ (run κ D mode tape).2+p.eval (n+D.demands.length+B+κ) := by
  let line : Polynomial ℕ := X*2+X*X
  let price := line+X+line*(2*X)+2
  let rows := 2*price+2*line+3
  let rounds : Polynomial ℕ := (X+2)*X+1
  refine ⟨rounds*(rows*roundControlBudget X),?_⟩
  intro n B κ D mode tape positive fits
  let x := n+D.demands.length+B+κ
  let input := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
  let cover := BinaryFractionalGuesses.solveInput input
  let reader := DirectBinaryEdgeWire.read cover.1
  have hn : n ≤ x := by dsimp only [x]; omega
  have hd : D.demands.length ≤ x := by dsimp only [x]; omega
  have hB : B ≤ x := by dsimp only [x]; omega
  have hk : κ ≤ x := by dsimp only [x]; omega
  have dim : lineSize n ≤ line.eval x := by
    simp only [line,eval_add,eval_mul,eval_X,eval_ofNat,lineSize]
    gcongr
  have stored := PhysicalEdgeSolver.line_size_le D positive fits
  rw [← PhysicalAmplifiedBinaryEdge.line_value D] at stored
  have boundedPrice : ChargedVertexModes.priceWidth input ≤ price.eval x := by
    have field := stored.trans (show PhysicalEdgeSolver.lineInputSizeBound n D.demands.length B ≤
        (line+X+line*(2*X)+1).eval x by
      simp only [PhysicalEdgeSolver.lineInputSizeBound,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
      gcongr)
    change OriginalStoreInitial.inputSize input.costs input.demands ≤ _ at field
    simp only [OriginalStoreInitial.inputSize,eval_add,eval_X,eval_one] at field
    simp only [ChargedVertexModes.priceWidth,price,eval_add,eval_X,eval_ofNat]
    omega
  have readerRows : ChargedPhysicalVertexSolver.rowsCount reader.1 ≤ rows.eval x := by
    have obs : reader.1=PhysicalCoverReader.plan cover.1 := DirectBinaryEdgeWire.read_value _
    rw [obs]
    refine (ChargedPhysicalVertexSolver.rowsCount_le input).trans
      ((PhysicalSolverCostEnvelope.rowLimit_le input (ChargedVertexModes.priceWidth_bounds input)).trans ?_)
    simp only [PhysicalSolverCostEnvelope.rowEnvelope,rows,eval_add,eval_mul,eval_ofNat]
    gcongr
  have samples : (BinarySolverOuterControls.edge n κ).extra+1 ≤ rounds.eval x := by
    rw [BinarySolverOuterControls.edge_extra]
    simp only [rounds,eval_add,eval_X,eval_mul,eval_ofNat,eval_one]
    apply Nat.add_le_add_right
    exact (PhysicalSolverCostEnvelope.exponent_le n κ).trans (by gcongr)
  have roundWork : roundControlBudget n ≤ (roundControlBudget X).eval x := by
    rw [roundControlBudget_eval,eval_X]
    exact roundControlBudget_mono hn
  have all := runWithRoundWork_extra κ D mode tape
  dsimp only at all
  apply all.trans
  simp only [eval_mul]
  exact Nat.add_le_add_left (Nat.mul_le_mul samples (Nat.mul_le_mul readerRows roundWork)) _

theorem wire_round_work_polynomial : ∃ p : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      (edgeWithRoundWork κ mode source tape).2 ≤ p.eval (source.length+κ) := by
  obtain ⟨baseline,old⟩ := wire_polynomial
  obtain ⟨p,extra⟩ := run_round_work_bound
  let pad : Polynomial ℕ := 3*X+1
  refine ⟨baseline+p.comp pad,?_⟩
  intro κ mode source tape
  let x := source.length+κ
  let parsed := PhysicalSourceInputJoin.edge source
  let legacy (data : Σ n,EncodedEdgeInput.Input n) : Read (Σ n,PhysicalAmplifiedEdgeSolver.EdgeResult n) :=
    let r := runOn κ mode data.2 tape
    (r.1.map (fun out => ⟨data.1,out⟩),r.2)
  let measured (data : Σ n,EncodedEdgeInput.Input n) : Read (Σ n,PhysicalAmplifiedEdgeSolver.EdgeResult n) :=
    let r := runOnWithRoundWork κ mode data.2 tape
    (r.1.map (fun out => ⟨data.1,out⟩),r.2)
  have before : edgeWithCost κ mode source tape=Read.bind parsed legacy := by
    unfold edgeWithCost
    congr 1
  have after : edgeWithRoundWork κ mode source tape=Read.bind parsed measured := by
    unfold edgeWithRoundWork
    congr 1
  have bound := old κ mode source tape
  rw [before] at bound
  rw [after]
  simp only [eval_add,eval_comp]
  refine le_trans ?_ (Nat.add_le_add_right bound (p.eval (pad.eval x)))
  have difference := PaidVertexSampling.bind_extra (d := 0) (e := p.eval (pad.eval x))
    (a := parsed) (b := parsed) (f := legacy) (g := measured) rfl (Nat.le_add_right _ _)
  apply le_trans (difference ?_)
  · simp only [Nat.add_zero]
    exact Nat.le_refl _
  rintro ⟨n,D⟩ read
  have original : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ := by
    rwa [ChargedSourceAssembly.edge_value,← PhysicalSourceInputJoin.edge_value]
  obtain ⟨dim,demands,fields⟩ := ChargedSourceAssembly.edge_dimensions original
  let raw := PhysicalBinaryEdgeWire.decodeWithCost D
  have words := decoded_widths D fields
  have lift : n+raw.1.demands.length+(source.length+1)+κ ≤ pad.eval x := by
    change n+D.demands.length+(source.length+1)+κ ≤ _
    simp only [pad,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    dsimp only [x]
    omega
  have paid := (extra κ raw.1 mode tape (Nat.le_add_left ..) words).trans
    (Nat.add_le_add_left (eval_mono p lift) _)
  simp only [legacy,measured,runOnWithRoundWork,runOn_reference]
  exact (Nat.add_le_add_left paid _).trans_eq (Nat.add_assoc ..).symm

end DirectedFlowCutGap.PaidDirectEdgeWire
