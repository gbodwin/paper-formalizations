import DirectedFlowCutGap.OracleMaskConstruction
import DirectedFlowCutGap.ActualDemandSelection

namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem same_label {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (u v : Fin n) : same (label u) (label v)=decide (u=v) :=
  SupportSearchEncoding.same_label label hlabel u v

theorem member_encode {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (u : Fin n) (es : List (Fin n × Fin n)) :
    member (label u) (es.map (fun e => (label e.1,label e.2)))=
      (BinaryFractionalGraphOracle.memberTail u es).1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,member,same_label label hlabel,BinaryFractionalGraphOracle.memberTail]
    by_cases h : e.1=u <;> simp [h,ih]

theorem bit_encode {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (s t u : Fin n) (es : List (Fin n × Fin n)) :
    bit (label s) (label t) (label u) (es.map (fun e => (label e.1,label e.2)))=
      (BinaryFractionalGraphOracle.internalMask s t es).1[u.val] := by
  simp only [bit,same_label label hlabel,BinaryFractionalGraphOracle.internalMask,
    EncodedRoundingInput.tabulate_get]
  by_cases hs : u=s <;> by_cases ht : u=t <;> simp [hs,ht,member_encode label hlabel]

theorem mask_encode {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (s t : Fin n) (es : List (Fin n × Fin n)) :
    mask (label s) (label t) (es.map (fun e => (label e.1,label e.2)))
        ((ResidualSearch.Enumeration.fin n).vertices.map label)=
      (BinaryFractionalGraphOracle.internalMask s t es).1.toList := by
  simp only [mask,List.map_map,Function.comp_def,bit_encode label hlabel]
  change (List.finRange n).map (fun u => (BinaryFractionalGraphOracle.internalMask s t es).1[u.val])=_
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

end DirectedFlowCutGap.OracleMask
