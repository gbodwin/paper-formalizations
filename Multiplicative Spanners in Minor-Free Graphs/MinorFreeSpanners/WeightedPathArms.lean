import MinorFreeSpanners.WeightedPathPrefixes

/-! Two actual threshold arms selected at an interior point of a given
simple path. Their only shared vertex is their common center. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

structure WeightedPathArms {I : Type*} (H : SimpleGraph I) (d : I → ℝ)
    (L D : ℝ) (x : I) where
  leftEnd : I
  rightEnd : I
  left : H.Walk x leftEnd
  right : H.Walk x rightEnd
  left_path : left.IsPath
  right_path : right.IsPath
  left_lower : L≤pathMass d left
  right_lower : L≤pathMass d right
  left_upper : pathMass d left<L+D
  right_upper : pathMass d right<L+D
  overlap : ∀ z∈left.support,z∈right.support → z=x

namespace WeightedPathArms
variable {I : Type*} {H : SimpleGraph I} {d : I → ℝ} {L D : ℝ} {x : I}

noncomputable def carrier (A : WeightedPathArms H d L D x) : Finset I := by
  classical
  exact A.left.support.toFinset∪A.right.support.toFinset

 theorem center_mem (A : WeightedPathArms H d L D x) : x∈A.carrier := by
  classical
  exact Finset.mem_union_left _ (List.mem_toFinset.mpr A.left.start_mem_support)

 theorem connected (A : WeightedPathArms H d L D x) : ConnectedWithin H A.carrier := by
  classical
  have reach : ∀ z∈A.carrier,∃ p : H.Walk x z,∀ v∈p.support,v∈A.carrier := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · let p := A.left.takeUntil z (List.mem_toFinset.mp hz)
      exact ⟨p,fun v hv => Finset.mem_union_left _
        (List.mem_toFinset.mpr (A.left.support_takeUntil_subset_support _ hv))⟩
    · let p := A.right.takeUntil z (List.mem_toFinset.mp hz)
      exact ⟨p,fun v hv => Finset.mem_union_right _
        (List.mem_toFinset.mpr (A.right.support_takeUntil_subset_support _ hv))⟩
  intro a ha b hb
  obtain ⟨p,hp⟩ := reach a ha
  obtain ⟨q,hq⟩ := reach b hb
  refine ⟨p.reverse.append q,?_⟩
  intro z hz
  rcases (Walk.mem_support_append_iff _ _).mp hz with hz|hz
  · exact hp z (by simpa using hz)
  · exact hq z hz

 theorem radial_path (A : WeightedPathArms H d L D x)
    (hd : ∀ v∈A.carrier,0≤d v) {z : I} (hz : z∈A.carrier) :
    ∃ p : H.Walk x z,p.IsPath ∧ (∀ v∈p.support,v∈A.carrier) ∧
      pathMass d p<L+D := by
  classical
  have hprefix : ∀ {y},∀ q : H.Walk x y,q.IsPath →
      q.support.toFinset⊆A.carrier → pathMass d q<L+D → z∈q.support →
      ∃ p : H.Walk x z,p.IsPath ∧ (∀ v∈p.support,v∈A.carrier) ∧
        pathMass d p<L+D := by
    intro y q hq hqs hmass hzq
    let p := q.takeUntil z hzq
    have hsub : p.support.toFinset⊆q.support.toFinset := by
      intro v hv
      exact List.mem_toFinset.mpr (q.support_takeUntil_subset_support hzq (List.mem_toFinset.mp hv))
    refine ⟨p,hq.takeUntil hzq,fun v hv => hqs (hsub (List.mem_toFinset.mpr hv)),?_⟩
    apply lt_of_le_of_lt _ hmass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun v hv _ => hd v (hqs hv))
  rcases Finset.mem_union.mp hz with hz|hz
  · exact hprefix A.left A.left_path Finset.subset_union_left A.left_upper (List.mem_toFinset.mp hz)
  · exact hprefix A.right A.right_path Finset.subset_union_right A.right_upper (List.mem_toFinset.mp hz)

 theorem mass (A : WeightedPathArms H d L D x) :
    2*L-d x≤∑ v∈A.carrier,d v := by
  classical
  have hi : A.left.support.toFinset∩A.right.support.toFinset={x} := by
    ext z
    simp only [Finset.mem_inter,List.mem_toFinset,Finset.mem_singleton]
    constructor
    · exact fun h => A.overlap z h.1 h.2
    · rintro rfl
      exact ⟨A.left.start_mem_support,A.right.start_mem_support⟩
  have he := Finset.sum_union_inter (s₁ := A.left.support.toFinset)
    (s₂ := A.right.support.toFinset) (f := d)
  rw [hi,Finset.sum_singleton] at he
  have hl := A.left_lower
  have hr := A.right_lower
  change 2*L-d x≤∑ v∈A.left.support.toFinset∪A.right.support.toFinset,d v
  dsimp [pathMass] at hl hr
  linarith

end WeightedPathArms

 theorem exists_weighted_path_arms {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (L D : ℝ) {a b x : I} (p : H.Walk a b)
    (hp : p.IsPath) (hx : x∈p.support) (hL : 0<L)
    (hd : ∀ v∈p.support,d v≤D)
    (hleft : L≤pathMass d (p.takeUntil x hx))
    (hright : L≤pathMass d (p.dropUntil x hx)) :
    ∃ A : WeightedPathArms H d L D x,A.carrier⊆p.support.toFinset := by
  classical
  let pl := p.takeUntil x hx
  let pr := p.dropUntil x hx
  have he : p=pl.append pr := (Walk.take_spec p hx).symm
  have hpl : pl.IsPath := hp.takeUntil hx
  have hpr : pr.IsPath := hp.dropUntil hx
  obtain ⟨u,q,qr,hq,hqp,hql,hqu⟩ := exists_weighted_path_prefix d D L pl.reverse
    hpl.reverse hL (fun v hv => hd v (p.support_takeUntil_subset_support hx (by simpa using hv)))
    (by simpa only [pathMass_reverse] using hleft)
  obtain ⟨v,r,rr,hr,hrp,hrl,hru⟩ := exists_weighted_path_prefix d D L pr
    hpr hL (fun v hv => hd v (p.support_dropUntil_subset_support hx hv)) hright
  have hqls : ∀ z∈q.support,z∈pl.support := by
    intro z hz
    have hz' : z∈pl.reverse.support := by rw [hq,Walk.mem_support_append_iff];exact Or.inl hz
    simpa using hz'
  have hrrs : ∀ z∈r.support,z∈pr.support := by
    intro z hz
    rw [hr,Walk.mem_support_append_iff]
    exact Or.inl hz
  let A : WeightedPathArms H d L D x := {
    leftEnd := u, rightEnd := v, left := q, right := r
    left_path := hqp, right_path := hrp
    left_lower := hql, right_lower := hrl
    left_upper := hqu, right_upper := hru
    overlap := by
      intro z hzq hzr
      by_contra hn
      exact ((he ▸ hp).ne_of_mem_support_of_append hn (hqls z hzq) (hrrs z hzr)) rfl }
  refine ⟨A,?_⟩
  intro z hz
  rcases Finset.mem_union.mp hz with hz|hz
  · exact List.mem_toFinset.mpr (p.support_takeUntil_subset_support hx (hqls z (List.mem_toFinset.mp hz)))
  · exact List.mem_toFinset.mpr (p.support_dropUntil_subset_support hx (hrrs z (List.mem_toFinset.mp hz)))

end MinorFreeSpanners
