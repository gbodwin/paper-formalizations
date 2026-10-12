import MinorFreeSpanners.ConnectedSetUnitCredits

/-! In an actual forest, every branching vertex has a real neighbor outside
any given simple path. This is the surplus vertex used by the low-degree phase. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem forest_walk_support_connected {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : ConnectedWithin G p.support.toFinset := by
  classical
  intro x hx y hy
  have hx' := List.mem_toFinset.mp hx
  have hy' := List.mem_toFinset.mp hy
  refine ⟨(p.takeUntil x hx').reverse.append (p.takeUntil y hy'),?_⟩
  intro z hz
  apply List.mem_toFinset.mpr
  rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact p.support_takeUntil_subset_support hx' (by simpa using hz)
  · exact p.support_takeUntil_subset_support hy' hz

 theorem acyclic_path_neighbors_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (x : V) :
    ((G.neighborFinset x).filter fun y => y∈p.support).card ≤ 2 := by
  classical
  let N := (G.neighborFinset x).filter fun y => y∈p.support
  by_cases hx : x∈p.support
  · obtain ⟨q,r,hq,hr,hqr⟩ := hp.mem_support_iff_exists_append.mp hx
    have hsub : N ⊆ {q.penultimate,r.snd} := by
      intro y hy
      obtain ⟨hyadj,hyp⟩ := Finset.mem_filter.mp hy
      have hxy : G.Adj x y := (G.mem_neighborFinset _ _).mp hyadj
      rw [hqr,Walk.mem_support_append_iff] at hyp
      rcases hyp with hyq | hyr
      · simp [hG.eq_penultimate_of_adj_end hq hxy hyq]
      · simp [hG.eq_snd_of_adj_start hr hxy hyr]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · by_cases hN : N.Nonempty
    · obtain ⟨y,hy⟩ := hN
      have hsub : N ⊆ {y} := by
        intro z hz
        obtain ⟨hyadj,hyp⟩ := Finset.mem_filter.mp hy
        obtain ⟨hzadj,hzp⟩ := Finset.mem_filter.mp hz
        obtain ⟨r,hrs,_⟩ := (forest_walk_support_connected p).short_walk
          (List.mem_toFinset.mpr hyp) (List.mem_toFinset.mpr hzp)
        let q := r.toPath
        have hqx : x∉q.val.support := by
          intro h
          exact hx (List.mem_toFinset.mp (hrs x (r.support_toPath_subset_support h)))
        have hpath := q.property.cons hqx (h := (G.mem_neighborFinset _ _).mp hyadj)
        have he := hG.eq_snd_of_adj_start hpath ((G.mem_neighborFinset _ _).mp hzadj)
          (by simp : z∈(Walk.cons ((G.mem_neighborFinset _ _).mp hyadj) q.val).support)
        simpa using he
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hc
      exact hc.trans (by decide)
    · have he : N=∅ := Finset.not_nonempty_iff_eq_empty.mp hN
      change N.card≤2
      simp [he]

 theorem branching_neighbor_off_path {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (x : V) (hx : 3≤G.degree x) :
    ∃ y, G.Adj x y ∧ y∉p.support := by
  classical
  by_contra hn
  push Not at hn
  have he : (G.neighborFinset x).filter (fun y => y∈p.support)=G.neighborFinset x := by
    apply Finset.filter_eq_self.mpr
    intro y hy
    exact hn y ((G.mem_neighborFinset _ _).mp hy)
  have hc := acyclic_path_neighbors_le_two G hG p hp x
  rw [he,SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega

end MinorFreeSpanners
