import DirectedFlowCutGap.BinaryPackingBudget
import DirectedFlowCutGap.BinaryWeightedPackingTrees
import DirectedFlowCutGap.QueryBudgetArithmetic

/-! A uniform finite-prefix bound for the actual packing body and its final
original-weight ticket. The bound holds for every returned history, including
bad-quality calls. Stored rational widths are explicit. -/
namespace DirectedFlowCutGap.BinaryPackingPrefixBudget
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryFractionalRows BinaryApproximatePacking
open BinaryApproximatePackingZeros BinaryZeroAvoidingProvider
open FiniteDrawTrees LazyFairBitTrees

private theorem width_value_le (xs : Bits) : FairBitWords.width (value xs) ≤ xs.length+1 :=
  QueryBudgetArithmetic.width_of_lt (value_lt xs)

theorem ticket_width {m S : ℕ} (w : Row m) (columns : Set (FractionalCover.Column m))
    (r : InputResult (auxiliary w) (zeroFreeColumns w columns))
    (hw : ∀ i,BinaryRational.StoredBounded (get w i) S) :
    FairBitWords.width (value (BinaryWeightedSampling.prepare
      (BinaryWeightedSampling.eventInput r.rest.state.events).1).total)  ≤  3*m^2*(S+1)+2 := by
  obtain ⟨hk,hs⟩ := event_original_widths r S hw
  have hi : ∀ x∈(BinaryWeightedSampling.eventInput r.rest.state.events).1,
      x.1.length ≤ m ∧ BinaryRational.StoredBounded x.2 S := by
    rw [BinaryWeightedSampling.eventInput_value]
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact ⟨by simp,hs e he⟩
  have hp := (BinaryWeightedSampling.prepare_widths _ S m hi).1
  have he : (BinaryWeightedSampling.eventInput r.rest.state.events).1.length =
      r.rest.state.events.length := by
    rw [BinaryWeightedSampling.eventInput_value,List.length_map]
  rw [he] at hp
  have hk' := Nat.mul_le_mul_right (S+1) hk
  exact (width_value_le _).trans (by omega)

variable {m Q S : ℕ} (w : Row m) (columns : Set (FractionalCover.Column m))
variable (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m)∉columns)
variable (draw : CutProvider FiniteDrawTrees.Tree columns)
variable (hdraw : ∀ c,Within Q (draw c))
variable (hw : ∀ i,BinaryRational.StoredBounded (get w i) S)

include hdraw in
theorem auxiliary_within (c : Row m) :
    Within Q (auxiliaryProvider w columns hS hempty draw c) := by
  unfold auxiliaryProvider
  dsimp only []
  exact within_bind (hdraw _) _ (r := 0) (fun _ => .pure 0 _)

include hdraw hw in
theorem run_within (fuel : Bits) :
    Within ((3*m^2+1)*Q+value fuel*(3*m^2*(S+1)+2))
      (BinaryWeightedPacking.run w columns hS hempty draw BinarySamplerTrees.bit fuel) := by
  unfold BinaryWeightedPacking.run
  dsimp only []
  have hp := BinaryPackingBudget.solve_within (auxiliary w) (zeroFreeColumns w columns)
    (auxiliaryProvider w columns hS hempty draw)
    (auxiliary_within w columns hS hempty draw hdraw)
  rw [(BinaryFractionalCore.parameters_spec _).1,(BinaryFractionalCore.dimension_spec _).1] at hp
  change Within ((3*m^2+1)*Q) _ at hp
  apply within_bind hp
  intro history
  have hs := BinaryTicketTrees.events_within history.rest.state.events fuel
  have hc := ticket_width w columns history hw
  have hs' := within_mono hs (Nat.mul_le_mul_left (value fuel) hc)
  exact within_bind hs' _ (r := 0) (fun _ => .pure 0 _)

include hdraw hw in
theorem confidence_within (resources width : Bits) :
    Within ((3*m^2+1)*Q+(2*value width+value resources+3)*(3*m^2*(S+1)+2))
      (BinaryWeightedPackingConfidence.run w columns hS hempty draw
        BinarySamplerTrees.bit resources width) := by
  unfold BinaryWeightedPackingConfidence.run
  dsimp only []
  have h := run_within w columns hS hempty draw hdraw hw
    (BinaryWeightedPackingConfidence.fuel resources width).1
  rw [BinaryWeightedPackingConfidence.fuel_value] at h
  exact within_bind h _ (r := 0) (fun _ => .pure 0 _)

end DirectedFlowCutGap.BinaryPackingPrefixBudget
