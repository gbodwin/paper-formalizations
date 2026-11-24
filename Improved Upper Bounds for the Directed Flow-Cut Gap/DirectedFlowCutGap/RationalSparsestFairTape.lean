import DirectedFlowCutGap.RationalSparsestEdgeExpectation

/-! Quantify the probability of exceeding twice a verified ideal expected
sparsity bound on a finite uniform tape. The extra term is the inherited
per-draw rejection error summed over the explicit draw bound. -/
namespace DirectedFlowCutGap.RationalSparsestFairTape

noncomputable section
open scoped NNReal ENNReal
open FiniteAmplification (probability expectedCost)
open FiniteDrawTrees (ideal)
open RationalSparsestEdgeRound (Mask tree drawBound tapeBudget round)
open RationalSparsestEdgeExpectation (law expectedSparsity)
open EncodedEdgeRounding (selectedEdges)

private theorem probability_map {A B : Type*} (p : PMF A) (f : A → B)
    (P : B → Prop) :
    probability (p.map f) P=probability p (fun a => P (f a)) := by
  unfold probability
  rw [PMF.toOuterMeasure_map_apply]
  rfl

attribute [local irreducible] EncodedEdgeGadget.build in
private theorem choice_bound {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode) :
    FiniteDrawTrees.Within (drawBound n) (tree D mode) := by
  let g := EncodedEdgeGadget.build D
  have nverts : g.size≤BinaryEdgeGadget.dimension n := by
    have h := BinaryEdgeGadget.size_le D
    rw [BinaryEdgeGadget.build_value] at h
    exact h
  have cap : EncodedUniformRounding.drawBound (4*g.size^2)≤drawBound n := by
    unfold drawBound EncodedUniformRounding.drawBound
    gcongr
  cases mode
  · exact FiniteDrawTrees.within_mono (FiniteDrawTrees.within_map (EncodedWeightedRounding.tree_within g.data) _) cap
  · exact FiniteDrawTrees.within_mono (FiniteDrawTrees.within_map (EncodedSizeRounding.tree_within g.data) _) cap

def bad {n : ℕ} (D : EncodedEdgeGadget.Input n) (P : Finset (Fin n × Fin n))
    (bound : ℝ) (result : Option (Mask n)) : Prop :=
  ∃ mask, result=some mask ∧ bound < (SparsestEdgeBridge.sparsity D.graph D.cost P (selectedEdges mask) : ℝ)

theorem probability_cost {n : ℕ} (D : EncodedEdgeGadget.Input n) (P : Finset (Fin n × Fin n))
    (mode : ChargedVertexModes.Mode) (T : ℕ) (bound : ℝ) (positive : 0<bound)
    (expected : expectedSparsity D P mode≤bound) :
    probability ((EncodedSolverBits.fairTape (tapeBudget n T)).map
      (fun bits => (round D mode T bits).map Prod.fst)) (bad D P (2*bound)) ≤
      1/2+(drawBound n : ℝ)*((1 : ℝ)/2)^T := by
  let _ : Fintype (RetainedGridState.Flags n) := EncodedUniformRounding.flagsFintype n
  let _ : Fintype (Mask n) := Fintype.ofEquiv (Fin n → RetainedGridState.Flags n)
    { toFun := Vector.ofFn, invFun := Vector.get
      left_inv := by intro f; funext i; exact Vector.getElem_ofFn i.isLt
      right_inv := by intro v; apply Vector.ext; intro i hi; exact Vector.getElem_ofFn hi }
  let sparsity (X : Finset (Fin n × Fin n)) : ℝ := SparsestEdgeBridge.sparsity D.graph D.cost P X
  let event (mask : Mask n) : Prop := 2*bound<sparsity (selectedEdges mask)
  rw [RationalSparsestEdgeRound.round_fairTape,probability_map]
  have asEvent : (fun a => bad D P (2*bound) (some a))=event := by
    funext a
    apply propext
    constructor
    · rintro ⟨mask,same,h⟩
      obtain rfl := Option.some.inj same
      exact h
    · exact fun h => ⟨a,rfl,h⟩
  rw [asEvent]
  have finite := LazyFairBitTrees.lowered_event_le (choice_bound D mode) T event
  refine finite.trans (add_le_add ?_ le_rfl)
  have idealEvent : probability (ideal (tree D mode)) event=
      probability (law D mode) (fun X => 2*bound<sparsity X) :=
    (probability_map (ideal (tree D mode)) selectedEdges (fun X => 2*bound<sparsity X)).symm
  rw [idealEvent]
  have estimate := FiniteAmplification.threshold_mul_probability_le_expectedCost (law D mode) sparsity
    (fun _ => NNReal.coe_nonneg _) (2*bound) (by positivity)
  have paid : (2*bound)*probability (law D mode) (fun X => 2*bound<sparsity X) ≤ (2*bound)*(1/2) :=
    (estimate.trans expected).trans_eq (by ring)
  exact le_of_mul_le_mul_left paid (by positivity)

end
end DirectedFlowCutGap.RationalSparsestFairTape
