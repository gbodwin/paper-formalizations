import DirectedFlowCutGap.GraphRecoverySize
import DirectedFlowCutGap.ActualGraphDiscovery

namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open SupportSearchEncoding GraphWalkExtension

def instructionBound (N W S : ℕ) : ℕ :=
  GraphDiscoveryProgram.discoveryBudget N W N S+CostedSupportProgram.recoveryCap N N W+24

theorem recoveryCap_mono (N W S T : ℕ) (h : S ≤ T) :
    CostedSupportProgram.recoveryCap N S W ≤ CostedSupportProgram.recoveryCap N T W := by
  unfold CostedSupportProgram.recoveryCap SupportRecoveryProgram.searchCap SupportRecoveryProgram.scanCap
  gcongr

theorem steps_bound {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (y : Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (W : ℕ) (hW : 1 ≤ W) (hw : sw.length ≤ W) (labels : ∀ i,(label i).length ≤ W)
    (rowWidths : ∀ q∈y.toList,StoredBounded q W) :
    steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      y.toList sw (label t) (label s)+1 ≤ instructionBound n W sw.length := by
  have hi : ∀ u∈E.vertices.map label,value u<y.toList.length := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    simpa only [hlabel,Vector.length_toList] using i.isLt
  have hv : ∀ u∈E.vertices.map label,u.length ≤ W ∧ value u ≤ n := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    exact ⟨labels i,by rw [hlabel];exact i.isLt.le⟩
  have ht : value (label t) ≤ n := by rw [hlabel];exact t.isLt.le
  have discovery := GraphDiscoveryProgram.minimize_bound (E.vertices.map label)
    (GraphRelaxationRefinement.matrix adjacency) y.toList sw (label t) (label s) W n hW rowWidths
    (labels t) ht (labels s) hi hv
  simp only [List.length_map,E.length_eq_card,Fintype.card_fin] at discovery
  have hm := GraphDiscoveryRefinement.minimize_eq E adjacency y s t sw hs label hlabel
  change GraphDiscoveryProgram.minimize _ _ _ _ _ _=_ at hm
  cases hq : (BinaryFractionalWalkOracle.minimize E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t).1 with
  | none =>
    unfold steps
    rw [hm,hq]
    simp only [Option.map_none,finishSteps]
    unfold instructionBound
    omega
  | some old =>
    have chosen : GraphDiscoveryProgram.minimize (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
        y.toList sw (label t) (label s)=some (GraphRelaxationRefinement.encode label old) := by
      rw [hm,hq];rfl
    have length := minimize_edge_length chosen
    simp only [GraphRelaxationRefinement.encode,List.length_map,E.length_eq_card,Fintype.card_fin] at length
    have recovery := (CostedSupportProgram.steps_bound E adjacency old.edges y s t sw hs label hlabel
      W hW hw labels rowWidths).trans (recoveryCap_mono n W old.edges.length n length)
    have encoded : (GraphRelaxationRefinement.encode label old).edges=
        old.edges.map (SupportSearchEncoding.encodeEdge label) := rfl
    rw [←encoded] at recovery
    unfold steps
    rw [chosen]
    simp only [finishSteps]
    unfold instructionBound
    omega

end DirectedFlowCutGap.GraphRecoveryController
