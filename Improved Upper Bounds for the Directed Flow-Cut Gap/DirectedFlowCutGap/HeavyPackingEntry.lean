import DirectedFlowCutGap.HeavyPackingJoin
import DirectedFlowCutGap.WeightedEmptyCutRuntime

/-! The actual original-weight empty-cut decision is the deterministic front
end of the concrete heavy-provider packing program. The full packing history
and sampler record are retained on the nonempty branch. Charges add the actual
decision and packing annotations; a polynomial bound for the resulting complete
program and physical storage/runtime remain separate. -/
namespace DirectedFlowCutGap.HeavyPackingEntry
noncomputable section
open scoped ENNReal NNReal
open BinaryArithmetic BinaryFractionalRows BinaryApproximatePackingSampling
open HeavyCutProvider

abbrev Output {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) :=
  Option (BinaryWeightedPacking.Output w (columns adjacency w)) × ℕ

def label {n : ℕ} {adjacency : RetainedGridState.PairFlags n} {w : Row n}
    (out : Output adjacency w) : Option Bits :=
  match out.1 with
  | none => some []
  | some packed => packed.selected.label

def cut {n : ℕ} {adjacency : RetainedGridState.PairFlags n} {w : Row n}
    (out : Output adjacency w) : Finset (Fin n) :=
  Finset.univ.filter fun i => (label out).any (coordinate i)=true

theorem empty_correct {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) :
    (WeightedEmptyCutDecision.vertexDecision adjacency w).1=true ↔
      (∅ : FractionalCover.Column n)∈columns adjacency w := by
  have hw : WeightedEmptyCutDecision.vertexWeights w=(input adjacency w w).weight := by
    funext i
    apply NNReal.coe_injective
    rw [input_weight]
    simp only [WeightedEmptyCutDecision.vertexWeights,WeightedEmptyCutDecision.realValue,
      FractionalCoverRawCore.rational,BinaryZeroAvoidingSelector.tableValue_apply]
    norm_cast
  have hg : BinaryFractionalWalkOracle.graph adjacency=(input adjacency w w).graph := rfl
  simpa only [hw,hg,columns,Set.mem_setOf_eq] using
    WeightedEmptyCutDecision.vertexDecision_correct adjacency w

private theorem positive_of_nonempty {n : ℕ} (adjacency : RetainedGridState.PairFlags n)
    (w : Row n) (h : (∅ : FractionalCover.Column n)∉columns adjacency w) : 0<n := by
  by_contra hn
  have hn0 : n=0 := Nat.eq_zero_of_not_pos hn
  subst n
  have hs := HeavyPackingJoin.support_valid adjacency w
  have he : ZeroAvoidingSelector.positiveSupport (BinaryZeroAvoidingSelector.tableValue w)=∅ :=
    by ext i; exact Fin.elim0 i
  apply h
  simpa only [BinaryZeroAvoidingProvider.SupportValid,he] using hs

/-- Both the decision and the complete selected packing record are retained. -/
def run {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) : PMF (Output adjacency w) :=
  let decision := WeightedEmptyCutDecision.vertexDecision adjacency w
  if h : decision.1=true then
    PMF.pure (none,decision.2+4)
  else
    (HeavyPackingJoin.run adjacency w B
      (fun he => h ((empty_correct adjacency w).mpr he)) resources width).map
      (fun packed => (some packed,decision.2+packed.operations+4))

/-- Actual validity and zero avoidance hold on every returned outcome in
both branches, with no positive vertex count or nonempty-cut premise. -/
theorem run_valid {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n) (B : ℕ)
    (resources width : Bits) {out : Output adjacency w}
    (hout : out∈(run adjacency w B resources width).support) :
    cut out∈columns adjacency w ∧
      ∀ i∈cut out,0<(BinaryRational.decode (get w i)).value := by
  by_cases h : (WeightedEmptyCutDecision.vertexDecision adjacency w).1=true
  · have he : out=(none,(WeightedEmptyCutDecision.vertexDecision adjacency w).2+4) := by
      simpa [run,h] using hout
    subst out
    have hc : cut ((none,(WeightedEmptyCutDecision.vertexDecision adjacency w).2+4) : Output adjacency w)=
        (∅ : Finset (Fin n)) := by simp [cut,label,coordinate]
    rw [hc]
    exact ⟨(empty_correct adjacency w).mp h,by simp⟩
  · have hempty : (∅ : FractionalCover.Column n)∉columns adjacency w :=
      fun he => h ((empty_correct adjacency w).mpr he)
    rw [run,dite_eq_right h] at hout
    obtain ⟨packed,hp,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    obtain ⟨q,hq,hvalid,hpos⟩ := HeavyPackingJoin.run_valid
      (positive_of_nonempty adjacency w hempty) adjacency w B hempty resources width hp
    have hc : cut (some packed,(WeightedEmptyCutDecision.vertexDecision adjacency w).2+packed.operations+4)=
        (BinaryFractionalCore.decodeChoice q).column := by
      ext i
      simp only [cut,Finset.mem_filter,Finset.mem_univ,true_and,label,hq,Option.any_some]
      exact coordinate_choice i q
    rw [hc]
    exact ⟨hvalid,hpos⟩

/-- The same uniform graph-size factor covers every original binary-weight
input, including empty cuts and zero vertices. No caller quality law remains. -/
theorem uniform_marginal :
    ∀ δ : ℝ,0<δ → ∃ K : ℝ,0<K ∧
      ∀ (n : ℕ) (adjacency : RetainedGridState.PairFlags n) (w : Row n)
        (B : ℕ) (_hwidth : ∀ i,(BinaryRational.decode (get w i)).Bounded B)
        (resources width : Bits) (_hm : value resources=n) (_hB : value width=B) (i : Fin n),
      ((run adjacency w B resources width).toOuterMeasure
        {out | (label out).any (coordinate i)=true}).toReal ≤
        K*(n:ℝ)^((1:ℝ)/3+δ)*(FractionalCover.value (BinaryApproximatePacking.capacities w) i : ℝ) := by
  intro δ hδ
  obtain ⟨K,hK,hmarginal⟩ := HeavyPackingJoin.uniform_marginal δ hδ
  refine ⟨K,hK,?_⟩
  intro n adjacency w B hwidth resources width hm hB i
  by_cases h : (WeightedEmptyCutDecision.vertexDecision adjacency w).1=true
  · rw [run,dite_eq_left h,PMF.toOuterMeasure_pure_apply]
    change (if false=true then (1:ℝ≥0∞) else 0).toReal ≤ _
    rw [if_neg Bool.false_ne_true,ENNReal.toReal_zero]
    positivity
  · rw [run,dite_eq_right h,PMF.toOuterMeasure_map_apply]
    exact hmarginal n (Nat.zero_lt_of_lt i.isLt) adjacency w B hwidth
      (fun he => h ((empty_correct adjacency w).mpr he)) resources width hm hB i

end
end DirectedFlowCutGap.HeavyPackingEntry
