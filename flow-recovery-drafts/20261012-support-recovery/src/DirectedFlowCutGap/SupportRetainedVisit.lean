import DirectedFlowCutGap.SupportRetainedScans

/-! The physical visit implements the literal original forward-update choice,
including first predecessor order and the same retained edge suffix. -/
namespace DirectedFlowCutGap.SupportSearchEncoding
open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open SupportRecoveryProgram

theorem visit_eq {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (es : List (Fin n × Fin n)) {t : Fin n}
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u : Fin n)
    (S : RetainedPathSearch.State (FractionalCoverPathOracle.supportGraph
      (BinaryFractionalWalkOracle.graph adjacency) es) t) :
    visit (GraphRelaxationRefinement.matrix adjacency) (es.map (encodeEdge label)) (label u)
      (encodeCodes label S.codes)=
      encodeCodes label (RetainedPathSearch.visit (BinaryFractionalWalkOracle.supportTest adjacency es) S u).1.codes := by
  have hl := lookup_entries label hlabel u S.legacy.entries
  rw [←encode_state_codes label S] at hl
  have hp := predecessor_entries adjacency es label hlabel u S.legacy.entries
  rw [←encode_state_codes label S] at hp
  unfold RetainedPathSearch.visit
  dsimp only
  split
  · rename_i hit hhit
    simp only [visit,hl,hhit,Option.map_some]
  · rename_i hnone
    split
    · rename_i hmiss
      simp only [visit,hl,hnone,Option.map_none,hp,hmiss]
    · rename_i hit hhit
      simp only [visit,hl,hnone,Option.map_none,hp,hhit,Option.map_some]
      simp only [RetainedPathSearch.State.addWithCost,encodeCodes,List.map_cons,encodeCode,encodeEntry]
      rw [S.coherent hit.1 hit.2.1]
      rfl

end DirectedFlowCutGap.SupportSearchEncoding
