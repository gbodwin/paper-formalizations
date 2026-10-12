import DirectedFlowCutGap.CostedSupportProgram
import DirectedFlowCutGap.MaterializedGraphPath

namespace DirectedFlowCutGap.CostedSupportProgram
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open SupportSearchEncoding

theorem project_encoding {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (es : List (Fin n×Fin n)) :
    MaterializedGraphPath.Encodes ((es.map (encodeEdge label)).map Prod.fst) es := by
  induction es with
  | nil => exact .nil
  | cons e es ih => exact .cons (hlabel e.1) ih

theorem recovered_encoding {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (es : List (Fin n×Fin n)) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    MaterializedGraphPath.Encodes
      ((edges (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
        (es.map (encodeEdge label)) sw (label t)).map Prod.fst)
      (RetainedPathSearch.search E (BinaryFractionalWalkOracle.supportTest adjacency es) s t).edges := by
  unfold edges
  rw [SupportSearchEncoding.search_eq adjacency es s t label hlabel E sw hs]
  exact project_encoding label hlabel _

theorem result_eq {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (es : List (Fin n×Fin n)) (y : Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    result (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      (es.map (encodeEdge label)) sw (label t) y.toList=
      GraphRelaxationRefinement.encode label
        (BinaryFractionalWalkOracle.recover E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t es).1 := by
  have hc := MaterializedGraphPath.costs_eq y s sw hs (recovered_encoding E adjacency es s t sw hs label hlabel)
  unfold result MaterializedPathSum.result
  rw [hc]
  unfold edges
  rw [SupportSearchEncoding.search_eq adjacency es s t label hlabel E sw hs]
  rfl

theorem recovered_length {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (es : List (Fin n×Fin n)) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    (edges (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      (es.map (encodeEdge label)) sw (label t)).length ≤ n := by
  unfold edges
  rw [SupportSearchEncoding.search_eq adjacency es s t label hlabel E sw hs,List.length_map]
  simpa only [Fintype.card_fin] using
    (RetainedPathSearch.search E (BinaryFractionalWalkOracle.supportTest adjacency es) s t).edges_length_le

theorem recovered_words {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (es : List (Fin n×Fin n)) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (W : ℕ) (labels : ∀ i,(label i).length ≤ W) :
    ∀ w∈(edges (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      (es.map (encodeEdge label)) sw (label t)).map Prod.fst,w.length ≤ W ∧ value w<n := by
  unfold edges
  rw [SupportSearchEncoding.search_eq adjacency es s t label hlabel E sw hs]
  intro w hw
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hw
  obtain ⟨uv,_,rfl⟩ := List.mem_map.mp he
  exact ⟨labels uv.1,by simp only [encodeEdge,hlabel];exact uv.1.isLt⟩

def recoveryCap (N S W : ℕ) : ℕ := SupportRecoveryProgram.searchCap N S W N+7*N+
  MaterializedPathSum.instructionBound N W N W+23

theorem steps_bound {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (es : List (Fin n×Fin n)) (y : Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (W : ℕ) (hW : 1 ≤ W) (hw : sw.length ≤ W) (labels : ∀ i,(label i).length ≤ W)
    (rowWidths : ∀ q∈y.toList,StoredBounded q W) :
    steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      (es.map (encodeEdge label)) sw (label t) y.toList+1 ≤ recoveryCap n es.length W := by
  have hv : ∀ u∈E.vertices.map label,SupportRecoveryProgram.WordBound W n u := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    exact ⟨labels i,by rw [hlabel];exact i.isLt.le⟩
  have ht : SupportRecoveryProgram.WordBound W n (label t) := ⟨labels t,by rw [hlabel];exact t.isLt.le⟩
  have he : ∀ e∈es.map (encodeEdge label),SupportRecoveryProgram.EdgeWidths W e := by
    intro e he
    obtain ⟨uv,_,rfl⟩ := List.mem_map.mp he
    exact ⟨labels uv.1,labels uv.2⟩
  have hsearch := SupportRecoveryProgram.search_steps_le W n _ (GraphRelaxationRefinement.matrix adjacency)
    _ sw (label t) hv ht hw he
  simp only [List.length_map,E.length_eq_card,Fintype.card_fin] at hsearch
  have words := recovered_words E adjacency es s t sw hs label hlabel W labels
  have len := recovered_length E adjacency es s t sw hs label hlabel
  have hsum := MaterializedPathSum.steps_bound y.toList sw _ W n hW rowWidths
    (fun w h => (words w h).1) (fun w h => by simpa using (words w h).2)
    (fun w h => (words w h).2.le)
  simp only [List.length_map] at hsum
  have mono : MaterializedPathSum.instructionBound
      (edges (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
        (es.map (encodeEdge label)) sw (label t)).length W n sw.length ≤
      MaterializedPathSum.instructionBound n W n W := by
    unfold MaterializedPathSum.instructionBound CanonicalRationalSum.instructionBound
    gcongr
  have hb := hsum.trans mono
  unfold steps recoveryCap
  omega

end DirectedFlowCutGap.CostedSupportProgram
