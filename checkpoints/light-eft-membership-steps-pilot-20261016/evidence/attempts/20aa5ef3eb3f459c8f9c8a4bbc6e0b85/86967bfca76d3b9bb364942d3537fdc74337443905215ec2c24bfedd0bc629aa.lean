import LightEFTSpanners.StoredWeightedForestExecution
import LightEFTSpanners.StoredCanonicalForestGuarantee

namespace LightEFTSpanners.StoredOriginalWeightLookup
attribute [local instance] Classical.propDecidable

noncomputable def originalBank {n : ℕ} (w : Sym2 (Fin n) → ℚ) : TypedBank n :=
  (Finset.univ : Finset (Sym2 (Fin n))).toList.map fun e => (e.out,w e)

theorem weight_map_out {n : ℕ} (w : Sym2 (Fin n) → ℚ) (e : Sym2 (Fin n))
    (es : List (Sym2 (Fin n))) (he : e∈es) :
    weight e (es.map fun d => (d.out,w d))=w e := by
  induction es with
  | nil => simp at he
  | cons d ds ih =>
    simp only [List.map_cons,weight]
    have hd : s(d.out.1,d.out.2)=d := d.out_eq
    rw [hd]
    by_cases h : e=d
    · simp [h]
    · simp only [h, ite_false]
      exact ih ((List.mem_cons.mp he).resolve_left h)

theorem originalBank_represents {n : ℕ} (w : Sym2 (Fin n) → ℚ) :
    (fun e => weight e (originalBank w))=w := by
  funext e
  apply weight_map_out
  simp

end LightEFTSpanners.StoredOriginalWeightLookup
