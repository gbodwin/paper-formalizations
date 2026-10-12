import MinorFreeSpanners.WeightedPathSplit

/-! Actual maximum-mass simple paths in a finite carrier, with no acyclicity
or longest-path oracle. The finite optimization ranges over genuine supports. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem exists_max_supported_path {I : Type*} (H : SimpleGraph I)
    (S : Finset I) (hne : S.Nonempty) (d : I → ℝ) :
    ∃ x∈S,∃ y∈S,∃ p : H.Walk x y,p.IsPath ∧
      (∀ z∈p.support,z∈S) ∧
      ∀ a b,∀ q : H.Walk a b,q.IsPath →
        (∀ z∈q.support,z∈S) → pathMass d q≤pathMass d p := by
  classical
  let good (T : Finset I) := ∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=T
  let candidates := S.powerset.filter good
  obtain ⟨s,hs⟩ := hne
  have hsingle : {s}∈candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (by simpa using hs),s,s,.nil,Walk.IsPath.nil,?_⟩
    simp
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image candidates (fun T => ∑ i∈T,d i) ⟨_,hsingle⟩
  have hTS := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  obtain ⟨x,y,p,hp,he⟩ := (Finset.mem_filter.mp hT).2
  have hps : ∀ z∈p.support,z∈S := fun z hz => hTS (he ▸ List.mem_toFinset.mpr hz)
  refine ⟨x,hps x p.start_mem_support,y,hps y p.end_mem_support,p,hp,hps,?_⟩
  intro a b q hq hqs
  have hmem : q.support.toFinset∈candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_,a,b,q,hq,rfl⟩
    exact fun z hz => hqs z (List.mem_toFinset.mp hz)
  have hh := hmax q.support.toFinset hmem
  simpa only [pathMass,he] using hh

end MinorFreeSpanners
