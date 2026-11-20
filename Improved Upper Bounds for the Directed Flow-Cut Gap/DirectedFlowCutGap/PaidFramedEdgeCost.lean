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
  have bound (u v : Fin n) :
      raw.1.costs[u.val][v.val].num.size ≤ source.length+1 ∧ raw.1.costs[u.val][v.val].den.size ≤ source.length+1 := by
    let i := finProdFinEquiv (u,v)
    let a := BinaryFractionalRows.get D.costs i
    obtain ⟨hn,hd⟩ := original i
    simp only [raw,PhysicalBinaryEdgeWire.decode_value,EncodedEdgeInput.decodeInput,
      Vector.getElem_ofFn,BinaryFractionalRows.decode_get]
    change (value a.num).size ≤ _ ∧ (value a.den).size ≤ _
    exact ⟨((Nat.size_le.mpr (value_lt a.num)).trans hn).trans (Nat.le_succ _),
      ((Nat.size_le.mpr (value_lt a.den)).trans hd).trans (Nat.le_succ _)⟩
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

end DirectedFlowCutGap.PaidDirectEdgeWire
