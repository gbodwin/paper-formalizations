import DirectedFlowCutGap.DirectBinaryEdgeCost

namespace DirectedFlowCutGap.DirectBinaryEdgeCost

open BinaryArithmetic BinaryRational Polynomial EncodedEdgeLineInput
open PhysicalAmplifiedEdgeSolver (EdgeResult)
open PhysicalIntegerRoundingCost (eval_mono)
open DirectBinaryEdgeWire

private theorem stored_member {n : ℕ} (D : EncodedEdgeInput.Input n) (i : Fin (n*n)) :
    BinaryFractionalRows.get D.costs i ∈ D.costs.toList := by
  change D.costs[i.val] ∈ D.costs.toList
  have hi : i.val<D.costs.toList.length := by simp only [Vector.length_toList,i.isLt]
  simpa only [Vector.getElem_toList] using List.getElem_mem hi

attribute [local irreducible] DirectBinaryEdgeWire.run

theorem wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits)
    {n : ℕ} {r : EdgeResult n}, (edgeWithCost κ mode source tape).1=some ⟨n,r⟩ →
      (edgeWithCost κ mode source tape).2+r.dispatch+r.readback+r.roundingAndSelection≤p.eval (source.length+κ) := by
  obtain ⟨q,paid⟩ := run_polynomial
  let pad : Polynomial ℕ := 3*X+1
  let decoding := PhysicalBinaryEdgeWire.decodeBudget (X : Polynomial ℕ) X
  refine ⟨ChargedSourceAssembly.parsePolynomial+decoding+q.comp pad,?_⟩
  intro κ mode source tape n r performed
  let x := source.length+κ
  let read := ChargedSourceAssembly.edge source
  change read.1.bind (fun a => (runOn κ mode a.2 tape).map
    (fun out => (⟨a.1,out⟩ : Σ i, EdgeResult i)))=some (⟨n,r⟩ : Σ i, EdgeResult i) at performed
  obtain ⟨⟨m,D⟩,found,tail⟩ := Option.bind_eq_some_iff.mp performed
  obtain ⟨observed,ran,eq⟩ := Option.map_eq_some_iff.mp tail
  cases eq
  obtain ⟨dim,demands,stored⟩ := ChargedSourceAssembly.edge_dimensions found
  let raw := PhysicalBinaryEdgeWire.decodeWithCost D
  have fields (i : Fin (m*m)) : StoredBounded (BinaryFractionalRows.get D.costs i) source.length :=
    stored _ (stored_member D i)
  have bound (u v : Fin m) :
      raw.1.costs[u.val][v.val].num.size ≤ source.length+1 ∧ raw.1.costs[u.val][v.val].den.size ≤ source.length+1 := by
    let i := finProdFinEquiv (u,v)
    let a := BinaryFractionalRows.get D.costs i
    obtain ⟨hn,hd⟩ := fields i
    simp only [raw,PhysicalBinaryEdgeWire.decode_value,EncodedEdgeInput.decodeInput,
      Vector.getElem_ofFn,BinaryFractionalRows.decode_get]
    change (value a.num).size≤_ ∧ (value a.den).size≤_
    exact ⟨((Nat.size_le.mpr (value_lt a.num)).trans hn).trans (Nat.le_succ _),
      ((Nat.size_le.mpr (value_lt a.den)).trans hd).trans (Nat.le_succ _)⟩
  obtain ⟨a,worked,rfl⟩ := Option.map_eq_some_iff.mp ran
  have xs : source.length≤x := Nat.le_add_right _ _
  have nx := dim.trans xs
  have cap : m+raw.1.demands.length+(source.length+1)+κ≤pad.eval x := by
    change m+D.demands.length+(source.length+1)+κ≤_
    simp only [pad,eval_add,eval_mul,eval_ofNat,eval_one,eval_X]
    omega
  have executed := (paid κ raw.1 mode tape (Nat.le_add_left ..) bound worked).trans (eval_mono q cap)
  have parser := ((ChargedSourceAssembly.edge_paid source).trans_eq
    (ChargedSourceAssembly.parsePolynomial_eval _).symm).trans (eval_mono _ xs)
  have loads : raw.2≤decoding.eval x := by
    apply (PhysicalBinaryEdgeWire.decode_paid D fields).trans
    simp only [decoding,PhysicalBinaryEdgeWire.decodeBudget,BinaryEdgeProjection.readbackBudget,
      eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X]
    gcongr
  simp only [eval_add,eval_comp]
  change read.2+a.dispatch+a.readback+(a.roundingAndSelection+raw.2)≤
    ChargedSourceAssembly.parsePolynomial.eval x+decoding.eval x+q.eval (pad.eval x)
  change read.2≤_ at parser
  omega

end DirectedFlowCutGap.DirectBinaryEdgeCost
