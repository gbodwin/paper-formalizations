import MinorFreeSpanners.RootedResidualGraph

/-! An actual simple root path visits one residual component; an arbitrary
simple path visits at most two. This controls which augmenting path donors
can intersect the chosen diameter reserve. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem root_avoiding_component_cover {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (root : I) (ports : Finset I) {x y : I}
    (p : (rootedResidualGraph H R root ports).Walk x y)
    (hS : ∀ i∈p.support,i∈insert root R) (hn : root∉p.support) :
    ∃ Q : (H.induce (R:Set I)).ConnectedComponent,
      ∀ i∈p.support,i∈ResidualComponents.block H R Q := by
  classical
  obtain ⟨q,hq,_⟩ := root_avoiding_transfer H R root ports p hn
  have hR : ∀ i∈q.support,i∈R := by
    intro i hi
    have hi' : i∈p.support := hq ▸ hi
    rcases Finset.mem_insert.mp (hS i hi') with he | he
    · exact (hn (he ▸ hi')).elim
    · exact he
  obtain ⟨Q,hQ⟩ := ResidualComponents.covers H R (hR x q.start_mem_support)
  refine ⟨Q,?_⟩
  simpa only [hq] using residual_walk_in_block H R Q q hQ hR

 theorem from_root_component_cover {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (root : I) (ports : Finset I) {y : I}
    (p : (rootedResidualGraph H R root ports).Walk root y) (hp : p.IsPath)
    (hS : ∀ i∈p.support,i∈insert root R) :
    ∃ Q : Finset (H.induce (R:Set I)).ConnectedComponent,Q.card≤1 ∧
      ∀ i∈p.support,i≠root → ∃ t∈Q,i∈ResidualComponents.block H R t := by
  classical
  cases p with
  | nil => exact ⟨∅,by simp,by simp⟩
  | cons h q =>
    obtain ⟨t,ht⟩ := root_avoiding_component_cover H R root ports q
      (fun i hi => hS i (by simp [hi])) ((Walk.cons_isPath_iff h q).mp hp).2
    refine ⟨{t},by simp,?_⟩
    intro i hi hn
    have hiq : i∈q.support := by simpa [hn] using hi
    exact ⟨t,by simp,ht i hiq⟩

 theorem simple_path_two_component_cover {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (root : I) (ports : Finset I) {x y : I}
    (p : (rootedResidualGraph H R root ports).Walk x y) (hp : p.IsPath)
    (hS : ∀ i∈p.support,i∈insert root R) :
    ∃ Q : Finset (H.induce (R:Set I)).ConnectedComponent,Q.card≤2 ∧
      ∀ i∈p.support,i≠root → ∃ t∈Q,i∈ResidualComponents.block H R t := by
  classical
  by_cases hr : root∈p.support
  · let l := p.takeUntil root hr
    let r := p.dropUntil root hr
    obtain ⟨Q,hQ,hQc⟩ := from_root_component_cover H R root ports l.reverse (hp.takeUntil hr).reverse
      (fun i hi => hS i (p.support_takeUntil_subset_support hr (by simpa using hi)))
    obtain ⟨T,hT,hTc⟩ := from_root_component_cover H R root ports r (hp.dropUntil hr)
      (fun i hi => hS i (p.support_dropUntil_subset_support hr hi))
    refine ⟨Q∪T,(Finset.card_union_le _ _).trans (by omega),?_⟩
    intro i hi hn
    have he : l.append r=p := Walk.take_spec p hr
    rw [←he,Walk.mem_support_append_iff] at hi
    rcases hi with hi | hi
    · obtain ⟨t,ht,hit⟩ := hQc i (by simpa using hi) hn
      exact ⟨t,Finset.mem_union_left _ ht,hit⟩
    · obtain ⟨t,ht,hit⟩ := hTc i hi hn
      exact ⟨t,Finset.mem_union_right _ ht,hit⟩
  · obtain ⟨t,ht⟩ := root_avoiding_component_cover H R root ports p hS hr
    exact ⟨{t},by simp,fun i hi _ => ⟨t,by simp,ht i hi⟩⟩

end MinorFreeSpanners
