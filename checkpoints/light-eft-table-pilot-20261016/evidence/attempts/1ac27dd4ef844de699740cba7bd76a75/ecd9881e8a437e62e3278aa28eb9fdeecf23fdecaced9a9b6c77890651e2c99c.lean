import LightEFTSpanners.StoredSortedCandidateExecutable
import LightEFTSpanners.StoredOriginalWeightedGuarantee

namespace LightEFTSpanners.StoredCandidateDrawLookup
attribute [local instance] Classical.propDecidable

noncomputable def originalBank {n : ℕ} (f : Sym2 (Fin n) → StoredDrawLookup.TypedBank n) : TypedBank n :=
  (Finset.univ : Finset (Sym2 (Fin n))).toList.map fun e => (e.out,f e)

theorem typedValue_map_out {n : ℕ} (f : Sym2 (Fin n) → StoredDrawLookup.TypedBank n) (e : Sym2 (Fin n))
    (es : List (Sym2 (Fin n))) (he : e∈es) :
    typedValue e (es.map fun d => (d.out,f d))=f e := by
  induction es with
  | nil => simp at he
  | cons d ds ih =>
    simp only [List.map_cons,typedValue]
    have hd : s(d.out.1,d.out.2)=d := d.out_eq
    rw [hd]
    by_cases h : e=d
    · simp [h]
    · simp only [h,ite_false]
      exact ih ((List.mem_cons.mp he).resolve_left h)

theorem originalBank_represents {n : ℕ} (f : Sym2 (Fin n) → StoredDrawLookup.TypedBank n) :
    (fun e => typedValue e (originalBank f))=f := by
  funext e
  apply typedValue_map_out
  simp
end LightEFTSpanners.StoredCandidateDrawLookup

namespace LightEFTSpanners.StoredOriginalCandidateRecords

theorem typedValue_filter {n : ℕ} (Q : List (Fin n × Fin n)) (bank : StoredCandidateDrawLookup.TypedBank n)
    (xs : List (Fin n × Fin n)) :
    typedValue Q bank xs=((xs.filter fun x => decide (s(x.1,x.2)∉StoredSample.edgeSet Q)).map
      fun x => (⟨x,StoredCandidateDrawLookup.typedValue s(x.1,x.2) bank⟩ : StoredForestBank.TypedInput n)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : s(x.1,x.2)∈StoredSample.edgeSet Q <;> simp [typedValue,h,ih]
end LightEFTSpanners.StoredOriginalCandidateRecords
