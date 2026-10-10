import DirectedFlowCutGap.RowInputBudgets
import DirectedFlowCutGap.ConstructedPackingPrefix

/-! Resource and confidence/stored-width words for the complete packing
prefix are obtained from actual supplied rational fields. This removes the
external metadata-word premises; input graph representation, fuel preparation
and full instruction-language compilation remain separate. -/
namespace DirectedFlowCutGap.StoredInputPackingPrefix
open BinaryArithmetic BinaryFractionalRows HeavyCutProvider

def budget {n : ℕ} (w : Row n) : Bits × ℕ :=
  let inputs := RowInputBudgets.prepare w
  let bound := EncodedPackingBitBudget.run inputs.resources inputs.width inputs.width
  (bound.1,inputs.operations+bound.2+8)

noncomputable section

theorem budget_value {n : ℕ} (w : Row n) :
    value (budget w).1=HeavyPackingBitBudget.polynomial n
      (BinaryInputBudgets.storedSize (RowInputBudgets.fields w))
      (BinaryInputBudgets.storedSize (RowInputBudgets.fields w)) := by
  have h := RowInputBudgets.prepare_spec w
  change value (EncodedPackingBitBudget.run _ _ _).1=_
  rw [ConstructedPackingPrefix.budget_value,h.1,h.2.1]

theorem budget_le_input_polynomial {n : ℕ} (w : Row n) :
    value (budget w).1 ≤
      HeavyPackingBitBudget.polynomial
        (BinaryInputBudgets.inputSize (RowInputBudgets.fields w))
        (BinaryInputBudgets.inputSize (RowInputBudgets.fields w))
        (BinaryInputBudgets.inputSize (RowInputBudgets.fields w)) := by
  have hs := BinaryInputBudgets.sizes (RowInputBudgets.fields w)
  rw [RowInputBudgets.fields_length] at hs
  have hn : n ≤ BinaryInputBudgets.inputSize (RowInputBudgets.fields w) := by omega
  have hb : BinaryInputBudgets.storedSize (RowInputBudgets.fields w) ≤
      BinaryInputBudgets.inputSize (RowInputBudgets.fields w) := by omega
  rw [budget_value]
  unfold HeavyPackingBitBudget.polynomial QueryBudgetArithmetic.polynomial
  gcongr

theorem output_law {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) :
    let inputs := RowInputBudgets.prepare w
    (FiniteBinaryPrefix.prefixLaw (value (budget w).1)).map
      (fun xs => ((HeavyPackingPrefix.read adjacency w (value inputs.width)
        inputs.resources inputs.width).run xs).1)=
      HeavyPackingEntry.run adjacency w (value inputs.width) inputs.resources inputs.width := by
  have h := RowInputBudgets.prepare_spec w
  exact ConstructedPackingPrefix.output_law adjacency w _ h.2.2.1 _ _ _ h.1 rfl rfl

/-- The uniform probability constant still precedes every input row. -/
theorem uniform_marginal :
    ∀ δ : ℝ,0 < δ → ∃ K : ℝ,0 < K ∧
      ∀ (n : ℕ) (adjacency : RetainedGridState.PairFlags n) (w : Row n) (i : Fin n),
        let inputs := RowInputBudgets.prepare w
        ((FiniteBinaryPrefix.prefixLaw (value (budget w).1)).toOuterMeasure
          {xs | (HeavyPackingEntry.label
            ((HeavyPackingPrefix.read adjacency w (value inputs.width)
              inputs.resources inputs.width).run xs).1).any
                (BinaryApproximatePackingSampling.coordinate i)=true}).toReal ≤
          K*(n : ℝ)^((1 : ℝ)/3+δ)*
            (FractionalCover.value (BinaryApproximatePacking.capacities w) i : ℝ) := by
  intro δ hδ
  obtain ⟨K,hK,h⟩ := HeavyPackingEntry.uniform_marginal δ hδ
  refine ⟨K,hK,?_⟩
  intro n adjacency w i
  have hs := RowInputBudgets.prepare_spec w
  have hi := h n adjacency w _ (fun i => stored_raw_bound (hs.2.2.1 i))
    _ _ hs.1 rfl i
  rw [← output_law adjacency w,PMF.toOuterMeasure_map_apply] at hi
  exact hi

/-- Combined declared input-scan and fixed binary-expression charges. -/
theorem construction_charge {n : ℕ} (w : Row n) :
    (budget w).1.length ≤ BinaryBudgetExpression.widthCoefficient EncodedPackingBitBudget.body*
      (2*BinaryInputBudgets.inputSize (RowInputBudgets.fields w)+1) ∧
    (budget w).2 ≤ 144*(BinaryInputBudgets.inputSize (RowInputBudgets.fields w)+1)^2+
      BinaryBudgetExpression.costCoefficient EncodedPackingBitBudget.body*
        (2*BinaryInputBudgets.inputSize (RowInputBudgets.fields w)+1)^2+8 := by
  obtain ⟨_,_,_,hr,hb,hc⟩ := RowInputBudgets.prepare_spec w
  have h := EncodedPackingBitBudget.run_bounds
    (RowInputBudgets.prepare w).resources (RowInputBudgets.prepare w).width
    (RowInputBudgets.prepare w).width (2*BinaryInputBudgets.inputSize (RowInputBudgets.fields w))
    (by omega) hb hb
  refine ⟨h.1,?_⟩
  change (RowInputBudgets.prepare w).operations+_
      +8 ≤ _
  omega

end
end DirectedFlowCutGap.StoredInputPackingPrefix
