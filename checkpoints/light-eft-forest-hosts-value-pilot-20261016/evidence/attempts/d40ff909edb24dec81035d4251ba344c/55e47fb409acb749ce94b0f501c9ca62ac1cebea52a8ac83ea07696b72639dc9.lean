import LightEFTSpanners.StoredFlagSampleExecutable
import LightEFTSpanners.BernoulliFlagLaw
import LightEFTSpanners.StoredSampleEncoding

namespace LightEFTSpanners.StoredFlagSample
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def entries {n : ℕ} (bits : Sym2 (Fin n) → Bool) : Input :=
  (univ : Finset (Sym2 (Fin n))).toList.map fun e => ((e.out.1.val,e.out.2.val),bits e)

noncomputable def typed {n : ℕ} (bits : Sym2 (Fin n) → Bool) : List (Fin n × Fin n) :=
  (((univ : Finset (Sym2 (Fin n))).toList).filter bits).map (fun e => e.out)

theorem execute_encoded {n : ℕ} (bits : Sym2 (Fin n) → Bool) :
    execute (entries bits)=StoredEdges.encode (typed bits) := by
  rw [execute_eq]
  unfold entries typed StoredEdges.encode
  rw [value_map,List.map_map]
  rfl

theorem typed_edgeSet {n : ℕ} (bits : Sym2 (Fin n) → Bool) :
    StoredSample.edgeSet (typed bits)=BernoulliFlags.selected bits := by
  ext e
  simp only [StoredSample.edgeSet,typed,List.mem_toFinset,List.mem_map,List.mem_filter,
    Finset.mem_toList,Finset.mem_univ,true_and,BernoulliFlags.mem_selected]
  constructor
  · rintro ⟨ab,⟨x,hx,rfl⟩,he⟩
    have h : x=e := x.out_eq.symm.trans he
    simpa only [h] using hx
  · intro he
    exact ⟨e.out,⟨e,he,rfl⟩,e.out_eq⟩
end LightEFTSpanners.StoredFlagSample
