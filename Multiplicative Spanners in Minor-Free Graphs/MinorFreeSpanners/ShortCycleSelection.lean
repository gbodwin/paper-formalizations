import MinorFreeSpanners.ShortCyclePaidCore

/-! Both outer threshold pieces are selected from the supplied actual simple
path. Trimming retains a contiguous subpath and the same middle heavy edge. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem exists_short_cycle_arms {I : Type*} {H : SimpleGraph I}
    (d : I → ℝ) (L D : ℝ) {u v x y : I}
    (l : H.Walk x u) (m : H.Walk x y) (r : H.Walk y v)
    (hp : (l.reverse.append (m.append r)).IsPath) (hL : 0<L)
    (hd : ∀ i∈(l.reverse.append (m.append r)).support,d i≤D)
    (hlongl : L≤pathMass (fun i => d i+1) l)
    (hlongr : L≤pathMass (fun i => d i+1) r)
    (hm : pathMass (fun i => d i+1) m≤2*(L+D+1)) :
    ∃ S : ShortCycleArms H d L D x y,
      S.middle=m ∧ S.carrier⊆(l.reverse.append (m.append r)).support.toFinset := by
  classical
  have hlp : l.IsPath := by simpa using hp.of_append_left.reverse
  have hrp : r.IsPath := hp.of_append_right.of_append_right
  obtain ⟨a,pl,tl,hl,hpl,hll,hlu⟩ := exists_weighted_path_prefix
    (fun i => d i+1) (D+1) L l hlp hL
    (fun i hi => by
      have hh := hd i (by simp only [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse];tauto)
      linarith) hlongl
  obtain ⟨b,pr,tr,hr,hpr,hrl,hru⟩ := exists_weighted_path_prefix
    (fun i => d i+1) (D+1) L r hrp hL
    (fun i hi => by
      have hh := hd i (by simp only [Walk.mem_support_append_iff];tauto)
      linarith) hlongr
  have he : l.reverse.append (m.append r)=
      tl.reverse.append ((pl.reverse.append (m.append pr)).append tr) := by
    rw [hl,hr,Walk.reverse_append]
    simp only [Walk.append_assoc]
  have hnew : (pl.reverse.append (m.append pr)).IsPath :=
    (he ▸ hp).of_append_right.of_append_left
  let S : ShortCycleArms H d L D x y := {
    leftEnd := a,rightEnd := b,left := pl,middle := m,right := pr,
    whole_path := hnew,left_lower := hll,right_lower := hrl,
    left_upper := by linarith,right_upper := by linarith,middle_upper := hm }
  refine ⟨S,rfl,?_⟩
  intro i hi
  have hi' : i∈(pl.reverse.append (m.append pr)).support := List.mem_toFinset.mp hi
  apply List.mem_toFinset.mpr
  rw [he,Walk.mem_support_append_iff,Walk.mem_support_append_iff]
  exact Or.inr (Or.inl hi')

end MinorFreeSpanners
