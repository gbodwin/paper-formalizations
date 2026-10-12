import MinorFreeSpanners.WeightedPathPrefixes

/-! Exact node-mass accounting and an actual balanced split of a simple
path. The split is chosen from the original walk, with no metric oracle. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem pathMass_takeUntil_le {I : Type*} {H : SimpleGraph I} (d : I → ℝ)
    {x y z : I} (p : H.Walk x y) (hz : z∈p.support)
    (hd : ∀ v∈p.support,0≤d v) : pathMass d (p.takeUntil z hz)≤pathMass d p := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    exact List.mem_toFinset.mpr (p.support_takeUntil_subset_support hz (List.mem_toFinset.mp hv))
  · intro v hv _
    exact hd v (List.mem_toFinset.mp hv)

 theorem pathMass_append {I : Type*} {H : SimpleGraph I} (d : I → ℝ)
    {x y z : I} (p : H.Walk x y) (q : H.Walk y z) (hpq : (p.append q).IsPath) :
    pathMass d (p.append q)+d y=pathMass d p+pathMass d q := by
  classical
  have hu : (p.append q).support.toFinset=p.support.toFinset∪q.support.toFinset := by
    ext v
    simp only [List.mem_toFinset,Finset.mem_union,Walk.mem_support_append_iff]
  have hi : p.support.toFinset∩q.support.toFinset={y} := by
    ext v
    simp only [Finset.mem_inter,List.mem_toFinset,Finset.mem_singleton]
    constructor
    · rintro ⟨hp,hq⟩
      by_contra hn
      exact (hpq.ne_of_mem_support_of_append hn hp hq) rfl
    · rintro rfl
      exact ⟨p.end_mem_support,q.start_mem_support⟩
  have h := Finset.sum_union_inter (s₁:=p.support.toFinset) (s₂:=q.support.toFinset) (f:=d)
  rw [hi,Finset.sum_singleton] at h
  simpa only [pathMass,hu] using h

 theorem exists_balanced_path_split {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (D : ℝ) {x y : I} (p : H.Walk x y) (hp : p.IsPath)
    (hd : ∀ v∈p.support,d v≤D) (hpos : 0<pathMass d p) :
    ∃ z,∃ q : H.Walk x z,∃ r : H.Walk z y,
      p=q.append r ∧ q.IsPath ∧ r.IsPath ∧
      pathMass d q≤pathMass d p/2+D ∧ pathMass d r≤pathMass d p/2+D := by
  classical
  obtain ⟨z,q,r,he,hq,hlo,hhi⟩ := exists_weighted_path_prefix d D (pathMass d p/2) p hp
    (by linarith) hd (by linarith)
  have hr : r.IsPath := (he ▸ hp).of_append_right
  have hmass := pathMass_append d q r (he ▸ hp)
  rw [← he] at hmass
  have hz : z∈p.support := by rw [he,Walk.mem_support_append_iff];exact Or.inl q.end_mem_support
  have hzD := hd z hz
  exact ⟨z,q,r,he,hq,hr,hhi.le,by linarith⟩

end MinorFreeSpanners
