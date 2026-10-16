import LightEFTSpanners.StoredFlagBatch

namespace LightEFTSpanners.StoredFlagBatch
open Controller
theorem next_trace (xs : Input) (acc : Output) : ∃ k,
    k≤(xs.map fun x => StoredFlagSample.bound x+2).sum+1 ∧
    Trace transition k (.next xs acc) (.reverse ((value xs).reverse++acc) []) := by
  induction xs generalizing acc with
  | nil => exact ⟨1,by simp,Trace.one rfl⟩
  | cons x xs ih =>
    obtain ⟨k,hk,ht⟩ := StoredFlagSample.full_trace x
    obtain ⟨m,hm,hr⟩ := ih (StoredFlagSample.value x::acc)
    have a := Trace.one (show transition (.next (x::xs) acc)=some (.sample xs acc (.scan x [])) from rfl)
    have b := sample_lift ht xs acc
    have c := Trace.one (show transition (.sample xs acc (.halt (StoredFlagSample.value x)))=
      some (.next xs (StoredFlagSample.value x::acc)) from rfl)
    refine ⟨((1+k)+1)+m,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons];omega
    · simpa [value] using ((a.trans b).trans c).trans hr

theorem sum_budget (xs : Input) :
    (xs.map fun x => StoredFlagSample.bound x+3).sum=
      (xs.map fun x => StoredFlagSample.bound x+2).sum+xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih];omega

theorem full_trace (xs : Input) : ∃ k,k≤budget xs ∧
    Trace transition k (.next xs []) (.halt (value xs)) := by
  obtain ⟨k,hk,ht⟩ := next_trace xs []
  have hr := reverse_trace (value xs).reverse []
  simp only [List.append_nil] at ht
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  refine ⟨k+((value xs).length+1),?_,ht.trans hr⟩
  have hs := sum_budget xs
  simp only [value,List.length_map] at *
  unfold budget;omega
end LightEFTSpanners.StoredFlagBatch
