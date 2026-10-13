import DirectedFlowCutGap.AvoidingShortestRefinement

namespace DirectedFlowCutGap.AvoidingShortest
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated

def inputSteps (n W S : ℕ) : ℕ := 5*n+49+GraphRecoveryController.instructionBound n W S

theorem zero_widths (n W : ℕ) (hW : 1≤W) : ∀ q∈(zeroRow n).toList,StoredBounded q W := by
  intro q hq
  simp [zeroRow] at hq
  rcases hq with ⟨_,rfl⟩
  simpa [StoredBounded,BinaryRational.zero] using hW

theorem steps_bound {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W) :
    steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t)+1≤
      inputSteps n W (label s).length := by
  have h := GraphRecoveryController.steps_bound E adjacency (zeroRow n) s t (label s) (hlabel s)
    label hlabel W hW (labels s) labels (zero_widths n W hW)
  simp only [steps,zeroRows_eq,List.length_map,E.length_eq_card,Fintype.card_fin]
  unfold inputSteps
  omega
end DirectedFlowCutGap.AvoidingShortest
