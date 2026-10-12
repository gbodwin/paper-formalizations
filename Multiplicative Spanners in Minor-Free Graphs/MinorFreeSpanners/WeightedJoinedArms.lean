import MinorFreeSpanners.SeparatedPathPieces

/-! Select the two threshold arms at the join of two actual simple path
pieces; all selected vertices remain in those original pieces. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem exists_weighted_joined_arms {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (L D : ℝ) {u v x : I} (l : H.Walk x u) (r : H.Walk x v)
    (hp : (l.reverse.append r).IsPath) (hL : 0<L)
    (hd : ∀ i∈(l.reverse.append r).support,d i≤D)
    (hleft : L≤pathMass d l) (hright : L≤pathMass d r) :
    ∃ P : WeightedPathArms H d L D x,P.carrier⊆(l.reverse.append r).support.toFinset := by
  classical
  have hlp : l.IsPath := by simpa using hp.of_append_left.reverse
  obtain ⟨a,pl,tl,hl,hpl,hll,hlu⟩ := exists_weighted_path_prefix d D L l hlp hL
    (fun i hi => hd i (by simp only [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse];tauto)) hleft
  obtain ⟨b,pr,tr,hr,hpr,hrl,hru⟩ := exists_weighted_path_prefix d D L r hp.of_append_right hL
    (fun i hi => hd i ((Walk.mem_support_append_iff _ _).mpr (Or.inr hi))) hright
  have hpls : ∀ i∈pl.support,i∈l.support := fun i hi => by
    rw [hl,Walk.mem_support_append_iff];exact Or.inl hi
  have hprs : ∀ i∈pr.support,i∈r.support := fun i hi => by
    rw [hr,Walk.mem_support_append_iff];exact Or.inl hi
  let P : WeightedPathArms H d L D x := {
    leftEnd := a,rightEnd := b,left := pl,right := pr,
    left_path := hpl,right_path := hpr,left_lower := hll,right_lower := hrl,
    left_upper := hlu,right_upper := hru,
    overlap := by
      intro z hz hz'
      by_contra hn
      exact (hp.ne_of_mem_support_of_append hn (by simpa using hpls z hz) (hprs z hz')) rfl }
  refine ⟨P,?_⟩
  intro i hi
  apply List.mem_toFinset.mpr
  rw [Walk.mem_support_append_iff]
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Or.inl (by simpa using hpls i (List.mem_toFinset.mp hi))
  · exact Or.inr (hprs i (List.mem_toFinset.mp hi))

end MinorFreeSpanners
