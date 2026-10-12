import DirectedFlowCutGap.SupportRetainedData
import DirectedFlowCutGap.GraphRelaxationRefinement

/-! Literal padded-label encoding for the original retained-data search. -/
namespace DirectedFlowCutGap.SupportSearchEncoding
open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open SupportRecoveryProgram

def encodeEdge {n : ℕ} (label : Fin n → Bits) (e : Fin n × Fin n) : Bits × Bits :=
  (label e.1,label e.2)
def encodeCode {n : ℕ} (label : Fin n → Bits) (x : Fin n × List (Fin n × Fin n)) : Code :=
  (label x.1,x.2.map (encodeEdge label))
def encodeCodes {n : ℕ} (label : Fin n → Bits) (xs : List (Fin n × List (Fin n × Fin n))) : List Code :=
  xs.map (encodeCode label)

theorem same_label {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (u v : Fin n) : same (label u) (label v)=decide (u=v) := by
  simp [same,GraphDiscoveryProgram.order_eq,hlabel,Fin.ext_iff]

theorem edgeEq_encode {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (e f : Fin n × Fin n) : edgeEq (encodeEdge label e) (encodeEdge label f)=decide (e=f) := by
  rcases e with ⟨u,v⟩
  rcases f with ⟨x,y⟩
  by_cases hu : u=x <;> by_cases hv : v=y <;>
    simp [encodeEdge,edgeEq,same_label label hlabel,hu,hv]

theorem member_encode {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (e : Fin n × Fin n) (es : List (Fin n × Fin n)) :
    member (encodeEdge label e) (es.map (encodeEdge label))=decide (e∈es) := by
  induction es with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons,member,edgeEq_encode label hlabel]
    by_cases he : f=e
    · subst f;simp
    · simp [he,Ne.symm he,ih]

theorem lookup_encode {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (u : Fin n) (xs : List (Fin n × List (Fin n × Fin n))) :
    lookup (label u) (encodeCodes label xs)=
      (xs.find? (fun x => decide (x.1=u))).map (encodeCode label) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeCodes,List.map_cons,lookup,encodeCode,same_label label hlabel,List.find?]
    by_cases he : x.1=u <;> simp [he,encodeCodes,encodeCode] at ih ⊢
    exact ih

theorem support_encode {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (es : List (Fin n × Fin n)) (u v : Fin n) :
    support (GraphRelaxationRefinement.matrix adjacency) (es.map (encodeEdge label)) (label u) (label v)=true ↔
      (FractionalCoverPathOracle.supportGraph (BinaryFractionalWalkOracle.graph adjacency) es).Adj u v := by
  change (GraphRelaxationProgram.adjacent (GraphRelaxationRefinement.matrix adjacency) (label u) (label v) &&
    member (encodeEdge label (u,v)) (es.map (encodeEdge label)))=true ↔ _
  rw [GraphRelaxationRefinement.adjacent_eq adjacency label hlabel,member_encode label hlabel]
  simp [BinaryFractionalWalkOracle.adjacent_value,FractionalCoverPathOracle.supportGraph]

end DirectedFlowCutGap.SupportSearchEncoding
