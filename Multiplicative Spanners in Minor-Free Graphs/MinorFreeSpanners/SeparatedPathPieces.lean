import MinorFreeSpanners.WeightedPathSplit
import MinorFreeSpanners.FourArmCore

/-! Two threshold end pieces of a genuinely long simple path leave a
nonempty middle gap. Their support separation is a path fact, not a premise. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem separated_path_supports {I : Type*} {H : SimpleGraph I}
    {a b c d : I} (p : H.Walk a b) (m : H.Walk b c) (q : H.Walk c d)
    (hp : (p.append (m.append q)).IsPath) (hm : ¬m.Nil) :
    Disjoint p.support.toFinset q.support.toFinset := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hzq
  have hpz := List.mem_toFinset.mp hz
  have hqz := List.mem_toFinset.mp hzq
  have hbc : b≠c := fun he => hm (hp.of_append_right.of_append_left.nil_iff_eq.mpr he)
  by_cases hzb : z=b
  · subst z
    exact (hp.of_append_right.ne_of_mem_support_of_append hbc m.start_mem_support hqz) rfl
  · exact (hp.ne_of_mem_support_of_append hzb hpz
      ((Walk.mem_support_append_iff _ _).mpr (Or.inr hqz))) rfl

 theorem exists_separated_path_pieces {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (D L : ℝ) {x y : I} (p : H.Walk x y) (hp : p.IsPath)
    (hL : 0<L) (hd0 : ∀ i∈p.support,0≤d i) (hd : ∀ i∈p.support,d i≤D)
    (hm : 2*(L+D)<pathMass d p) :
    ∃ a b,∃ l : H.Walk x a,∃ m : H.Walk a b,∃ r : H.Walk b y,
      p=l.append (m.append r) ∧ ¬m.Nil ∧
      L≤pathMass d l ∧ pathMass d l<L+D ∧
      L≤pathMass d r ∧ pathMass d r<L+D := by
  classical
  have hD : 0≤D := (hd0 x p.start_mem_support).trans (hd x p.start_mem_support)
  obtain ⟨a,l,t,he,_,hll,hlu⟩ := exists_weighted_path_prefix d D L p hp hL hd (by linarith)
  have ht : t.IsPath := (he ▸ hp).of_append_right
  have ha : a∈p.support := by rw [he,Walk.mem_support_append_iff];exact Or.inl l.end_mem_support
  have heq := pathMass_append d l t (he ▸ hp)
  rw [←he] at heq
  have htm : L+D<pathMass d t := by linarith [hd0 a ha]
  obtain ⟨b,r,m,hr,_,hrl,hru⟩ := exists_weighted_path_prefix d D L t.reverse ht.reverse hL
    (fun i hi => hd i (by rw [he,Walk.mem_support_append_iff];exact Or.inr (by simpa using hi)))
    (by simpa only [pathMass_reverse] using (show L≤pathMass d t by linarith))
  have htq : t=m.reverse.append r.reverse := by
    have hh := congrArg Walk.reverse hr
    simpa only [Walk.reverse_reverse,Walk.reverse_append] using hh
  have hmn : ¬m.reverse.Nil := by
    intro hn
    have hmnil : m.Nil := by simpa using hn
    cases m with
    | nil =>
      have hmass : pathMass d t=pathMass d r := by
        rw [htq]
        simp only [Walk.reverse_nil,Walk.nil_append,pathMass_reverse]
      linarith
    | cons h m => exact Walk.not_nil_cons hmnil
  exact ⟨a,b,l,m.reverse,r.reverse,by rw [he,htq],hmn,hll,hlu,
    by simpa only [pathMass_reverse] using hrl,by simpa only [pathMass_reverse] using hru⟩

end MinorFreeSpanners
