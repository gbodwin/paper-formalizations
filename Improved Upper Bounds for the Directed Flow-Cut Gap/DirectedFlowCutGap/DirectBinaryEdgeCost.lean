import DirectedFlowCutGap.BinaryFractionalWorkPolynomial
import DirectedFlowCutGap.DirectBinaryEdgeWire

namespace DirectedFlowCutGap.DirectBinaryEdgeCost

open BinaryArithmetic BinaryRational Polynomial EncodedEdgeLineInput
open PhysicalAmplifiedEdgeSolver (EdgeResult)
open PhysicalIntegerRoundingCost (eval_mono)
open DirectBinaryEdgeWire

attribute [local irreducible] DirectBinaryEdgeWire.run PhysicalAmplifiedBinaryEdge.lineWithCost
  BinaryFractionalWorkPolynomial.envelope PhysicalSourceDispatch.instructionPolynomial

private theorem scalar_list (xs : List Fraction) :
    (xs.map fun q => q.num.length+q.den.length+1).sum=LambdaRowProgram.rowBits xs+xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,LambdaRowProgram.rowBits,List.length_cons,ih]
    omega

private theorem scalar_size {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    BinaryFractionalGuessesBounds.scalarSize D.costs≤OriginalStoreInitial.inputSize D.costs D.demands := by
  unfold BinaryFractionalGuessesBounds.scalarSize OriginalStoreInitial.inputSize
  rw [scalar_list,Vector.length_toList]
  omega


private theorem sizes {n B : ℕ} (D : Input n) (z : ℕ) (pos : 1≤B)
    (hn : n≤z) (hd : D.demands.length≤z) (hb : B≤z)
    (fits : ∀ u v : Fin n, D.costs[u.val][v.val].num.size≤B ∧ D.costs[u.val][v.val].den.size≤B) :
    let L := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
    lineSize n≤128*(z+1)^4 ∧ L.demands.length≤128*(z+1)^4 ∧
      BinaryFractionalGuessesBounds.scalarSize L.costs≤128*(z+1)^4 ∧
      (PhysicalSourceDispatch.input L).length≤128*(z+1)^4 := by
  let a := z+1
  let L := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
  have nle : n≤a := hn.trans (Nat.le_succ _)
  have dle : D.demands.length≤a := hd.trans (Nat.le_succ _)
  have ble : B≤a := hb.trans (Nat.le_succ _)
  have mono (i j : ℕ) (h : i≤j) : a^i≤a^j := Nat.pow_le_pow_right (by unfold a; omega) h
  have one : 1≤a^4 := mono 0 4 (by decide)
  have a4 : a≤a^4 := by simpa only [pow_one] using mono 1 4 (by decide)
  have a2 : a^2≤a^4 := mono 2 4 (by decide)
  have a3 : a^3≤a^4 := mono 3 4 (by decide)
  have a23 : a^2≤a^3 := mono 2 3 (by decide)
  have a13 : a≤a^3 := by simpa only [pow_one] using mono 1 3 (by decide)
  have one3 : 1≤a^3 := mono 0 3 (by decide)
  have sq : a≤a^2 := by simpa only [pow_one] using mono 1 2 (by decide)
  have line : lineSize n≤3*a^2 := by
    unfold lineSize
    calc
      _ ≤ a*2+a*a := by gcongr
      _ ≤ _ := by nlinarith only [sq]
  have packed : PhysicalEdgeSolver.lineInputSizeBound n D.demands.length B≤12*a^3 := by
    unfold PhysicalEdgeSolver.lineInputSizeBound
    calc
      _ ≤ 3*a^2+a+3*a^2*(2*a)+1 := by gcongr
      _ ≤ _ := by nlinarith only [a23,a13,one3]
  have encoded : PhysicalSourceSizeBounds.lineSourceSizeBound n D.demands.length B≤128*a^4 := by
    unfold PhysicalSourceSizeBounds.lineSourceSizeBound PhysicalSourceSizeBounds.sourceSizeBound
    dsimp only
    calc
      _ ≤ 2*(12*a^3+(3*a^2)*(3*a^2)+a*(3*a^2+3*a^2))+3*(3*a^2+3*a^2+a)+3 := by gcongr
      _ ≤ _ := by nlinarith only [a2,a3,a4,one]
  have listSize : L.demands.length=D.demands.length := by
    simp only [L,PhysicalAmplifiedBinaryEdge.line_value,PhysicalEdgeSolver.binaryLineInput,lineInput,List.length_map]
  have scalar := PhysicalEdgeSolver.line_size_le D pos fits
  rw [← PhysicalAmplifiedBinaryEdge.line_value D] at scalar
  have payload : BinaryFractionalGuessesBounds.scalarSize L.costs≤12*a^3 :=
    (scalar_size L).trans (scalar.trans packed)
  change lineSize n≤128*a^4 ∧ L.demands.length≤128*a^4 ∧
    BinaryFractionalGuessesBounds.scalarSize L.costs≤128*a^4 ∧
    (PhysicalSourceDispatch.input L).length≤128*a^4
  refine ⟨line.trans (by omega),?_,payload.trans (by omega),?_⟩
  · rw [listSize]
    exact dle.trans (by omega)
  · change (PhysicalSourceDispatch.input (PhysicalAmplifiedBinaryEdge.lineWithCost D).1).length ≤ _
    rw [PhysicalAmplifiedBinaryEdge.line_value]
    exact (PhysicalSourceSizeBounds.line_source_size_le D pos fits).trans encoded

set_option maxHeartbeats 500000 in
theorem run_polynomial : ∃ p : Polynomial ℕ, ∀ {n B : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits), 1≤B →
    (∀ u v : Fin n, D.costs[u.val][v.val].num.size≤B ∧ D.costs[u.val][v.val].den.size≤B) →
    ∀ {r : EdgeResult n}, run κ D mode tape=some r →
      r.dispatch+r.readback+r.roundingAndSelection≤p.eval (n+D.demands.length+B+κ) := by
  obtain ⟨q,roundPaid⟩ := run_rounding_polynomial
  let length : Polynomial ℕ := 128*(X+1)^4
  let cardinality := 1+PhysicalSourceDispatch.instructionPolynomial.comp length
  refine ⟨BinaryFractionalWorkPolynomial.envelope.comp length+rowBudget length cardinality cardinality+q,?_⟩
  intro n B κ D mode tape positive fields r ran
  let y := n+D.demands.length+B+κ
  let L := (PhysicalAmplifiedBinaryEdge.lineWithCost D).1
  have hn : n≤y := by unfold y; omega
  have hd : D.demands.length≤y := by unfold y; omega
  have hb : B≤y := by unfold y; omega
  obtain ⟨nodes,ds,scalar,sourceSize⟩ := sizes D y positive hn hd hb fields
  have lengthValue : length.eval y=128*(y+1)^4 := by
    simp only [length,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
  have cap : 1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input L).length≤
      cardinality.eval y := by
    simp only [cardinality,eval_add,eval_one,eval_comp]
    exact Nat.add_le_add_left (eval_mono _ (sourceSize.trans_eq lengthValue.symm)) 1
  have bounds := run_prefix_paid κ D mode tape ran
  have dispatch := bounds.1.trans (BinaryFractionalWorkPolynomial.bound
    (nodes.trans_eq lengthValue.symm) (ds.trans_eq lengthValue.symm) (scalar.trans_eq lengthValue.symm))
  have readback : r.readback≤(rowBudget length cardinality cardinality).eval y := by
    apply bounds.2.trans
    simp only [rowBudget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]
    rw [lengthValue]
    gcongr
  have rounded : r.roundingAndSelection≤q.eval y := roundPaid κ D mode tape positive fields ran
  simp only [eval_add,eval_comp]
  change r.dispatch+r.readback+r.roundingAndSelection≤
    BinaryFractionalWorkPolynomial.envelope.eval (length.eval y)+(rowBudget length cardinality cardinality).eval y+q.eval y
  omega

end DirectedFlowCutGap.DirectBinaryEdgeCost
