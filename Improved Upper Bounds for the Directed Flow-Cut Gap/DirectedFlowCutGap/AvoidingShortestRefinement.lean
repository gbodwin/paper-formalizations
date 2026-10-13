import DirectedFlowCutGap.AvoidingShortestTrace

namespace DirectedFlowCutGap.AvoidingShortest
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation BooleanTableRead GraphWalkExtension

def zeroRow (n : ℕ) : Row n := Vector.replicate n BinaryRational.zero

theorem zeroRows_eq {n : ℕ} (E : ResidualSearch.Enumeration (Fin n)) (label : Fin n → Bits) :
    zeroRows (E.vertices.map label)=(zeroRow n).toList := by
  simp [zeroRows,zeroRow,E.length_eq_card]

theorem result_original {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    result (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t)=
      (BinaryFractionalWalkOracle.shortest E adjacency (BinaryFractionalGraphOracle.outgoing (zeroRow n) s) s t).1.map
        (GraphRelaxationRefinement.encode label) := by
  unfold result
  rw [zeroRows_eq]
  exact GraphRecoveryController.result_eq E adjacency (zeroRow n) s t (label s) (hlabel s) label hlabel

theorem typed_return {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {heap : NaturalHeap} {a b : ℕ}
    (input : GraphDiscoveryProgram.Vertices heap a (E.vertices.map label))
    (metadata : AvoidingZeroContext.Static heap b (GraphRelaxationRefinement.matrix adjacency) (label s) (label t))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1440)
    (stack : List (Frame ℕ 1440)) (source : Bits) :
    ∃ ext root,ext.length=cells (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t) ∧
      NaturalRun program (steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t))
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1410) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        ((BinaryFractionalWalkOracle.shortest E adjacency (BinaryFractionalGraphOracle.outgoing (zeroRow n) s) s t).1.map
          (GraphRelaxationRefinement.encode label)) := by
  have rows : n≤(GraphRelaxationRefinement.matrix adjacency).length := by simp [GraphRelaxationRefinement.matrix_length]
  have cols : ∀ (i : ℕ) (hi : i<n),n≤((GraphRelaxationRefinement.matrix adjacency)[i]'(lt_of_lt_of_le hi rows)).length := by
    intro i hi
    exact (GraphRelaxationRefinement.matrix_row_length adjacency ⟨i,hi⟩).ge
  have hv : ∀ u∈E.vertices.map label,value u<n := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    rw [hlabel];exact i.isLt
  have ht : value (label t)<n := by rw [hlabel];exact t.isLt
  have hc : ∀ u∈E.vertices.map label,value u<(E.vertices.map label).length := by
    simpa only [List.length_map,E.length_eq_card,Fintype.card_fin] using hv
  have valid := GraphRecoveryController.recovery_valid E adjacency (zeroRow n) s t (label s) (hlabel s) label hlabel
  obtain ⟨ext,root,len,run,rep⟩ := search_return n input metadata rows cols hv ht hc
    (by simpa only [zeroRows_eq,Vector.length_toList,List.length_map,E.length_eq_card,Fintype.card_fin] using valid)
    next c d hn saved pc stack source
  exact ⟨ext,root,len,run,by simpa only [result_original E adjacency s t label hlabel] using rep⟩
end DirectedFlowCutGap.AvoidingShortest
