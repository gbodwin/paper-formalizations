import DirectedFlowCutGap.SupportSearchEncoding

namespace DirectedFlowCutGap.SupportSearchEncoding
open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open SupportRecoveryProgram

def encodeEntry {n : ℕ} {G : Digraph (Fin n)} {t : Fin n} (label : Fin n → Bits)
    (e : ResidualSearch.Entry G t) : Code := encodeCode label (e.1,FlowTable.edgeList e.2)

theorem encode_state_codes {n : ℕ} {G : Digraph (Fin n)} {t : Fin n}
    (label : Fin n → Bits) (S : RetainedPathSearch.State G t) :
    encodeCodes label S.codes=S.legacy.entries.map (encodeEntry label) := by
  rw [SupportRetainedData.state_codes]
  simp only [encodeCodes,List.map_map,Function.comp_def]
  rfl

theorem lookup_entries {n : ℕ} {G : Digraph (Fin n)} {t : Fin n}
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u : Fin n)
    (xs : List (ResidualSearch.Entry G t)) :
    lookup (label u) (xs.map (encodeEntry label))=
      (CountedSearch.scan (fun e : ResidualSearch.Entry G t => e.1=u)
        (fun e => (inferInstanceAs (Decidable (e.1=u)),1)) xs).1.map
        (fun e => encodeEntry label e.1) := by
  rw [SupportRetainedData.counted_scan_find]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,lookup,encodeEntry,encodeCode,same_label label hlabel,List.find?]
    by_cases he : x.1=u <;> simp [he,encodeEntry,encodeCode] at ih ⊢
    exact ih

theorem predecessor_entries {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (es : List (Fin n × Fin n)) {t : Fin n}
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (u : Fin n)
    (xs : List (ResidualSearch.Entry (FractionalCoverPathOracle.supportGraph
      (BinaryFractionalWalkOracle.graph adjacency) es) t)) :
    predecessor (GraphRelaxationRefinement.matrix adjacency) (es.map (encodeEdge label)) (label u)
      (xs.map (encodeEntry label))=
      (CountedSearch.scan (fun e => (FractionalCoverPathOracle.supportGraph
        (BinaryFractionalWalkOracle.graph adjacency) es).Adj u e.1)
        (fun e => BinaryFractionalWalkOracle.supportTest adjacency es u e.1) xs).1.map
        (fun e => encodeEntry label e.1) := by
  rw [SupportRetainedData.counted_scan_find]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,SupportRecoveryProgram.predecessor,encodeEntry,encodeCode,List.find?]
    simp only [support_encode adjacency label hlabel]
    by_cases he : (FractionalCoverPathOracle.supportGraph
      (BinaryFractionalWalkOracle.graph adjacency) es).Adj u x.1 <;>
      simp [he,encodeEntry,encodeCode] at ih ⊢
    exact ih

end DirectedFlowCutGap.SupportSearchEncoding
