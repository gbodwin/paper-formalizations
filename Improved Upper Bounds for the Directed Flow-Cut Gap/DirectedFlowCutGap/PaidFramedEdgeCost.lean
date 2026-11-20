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

end DirectedFlowCutGap.PaidDirectEdgeWire
