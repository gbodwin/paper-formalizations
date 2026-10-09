import DegreeFaultSpanners.Construction
import DegreeFaultSpanners.CycleObstruction
import DegreeFaultSpanners.Blowup

/-! Assembly of the actual finite-field graph's matching obstruction. -/

namespace DegreeFaultSpanners

open SimpleGraph

variable {F : Type*} [Field F] {d : ℕ}

/-- Every alternate walk after deleting the matching is longer than the target stretch. -/
theorem matchingGraph_long {a : Point F d} {l : Line F d} (ha : a ∈ lineSet l)
    (p : (incidenceGraph F d \ matchingGraph a l).Walk (Sum.inl a) (Sum.inr l)) :
    2 * (d + 2) - 1 < p.length := by
  classical
  by_contra h
  have hshort : p.length ≤ 2 * (d + 2) - 1 := Nat.le_of_not_gt h
  let q := p.bypass
  let qG := q.mapLe (show incidenceGraph F d \ matchingGraph a l ≤ incidenceGraph F d from sdiff_le)
  have hqpath : q.IsPath := p.bypass_isPath
  have hqGpath : qG.IsPath := hqpath.mapLe _
  have hnotQ : s(Sum.inl a, Sum.inr l) ∉ q.edges := by
    intro he
    exact (q.adj_of_mem_edges he).2 (matchingGraph_target a l)
  have hnotG : s(Sum.inl a, Sum.inr l) ∉ qG.reverse.edges := by
    simpa only [qG, SimpleGraph.Walk.edges_reverse, List.mem_reverse,
      SimpleGraph.Walk.edges_mapLe_eq_edges] using hnotQ
  have hal : (incidenceGraph F d).Adj (Sum.inl a) (Sum.inr l) := ha
  let c0 : (incidenceGraph F d).Walk (Sum.inl a) (Sum.inl a) :=
    .cons hal qG.reverse
  have hc0 : c0.IsCycle :=
    SimpleGraph.Path.cons_isCycle
      (⟨qG.reverse, hqGpath.reverse⟩ : (incidenceGraph F d).Path (Sum.inr l) (Sum.inl a)) hal hnotG
  let c := c0.reverse
  have hc : c.IsCycle := hc0.reverse
  have hclen : c.length ≤ 2 * (d + 2) := by
    have hqle : q.length ≤ p.length := p.length_bypass_le_length
    simp only [c, c0, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_cons,
      qG, SimpleGraph.Walk.length_mapLe]
    omega
  let e := incidenceWalkEncoding c
  have hcyclelen := hc.three_le_length
  have hlen := e.length_eq
  have hrpos : 0 < e.halfLength := by omega
  let ref : Fin e.halfLength := ⟨e.halfLength - 1, by omega⟩
  have hreflast : ref.val + 1 = e.halfLength := by dsimp [ref]; omega
  have hrefget : c.getVert (2 * ref.val + 1) = Sum.inr l := by
    change c0.reverse.getVert _ = _
    rw [SimpleGraph.Walk.getVert_reverse]
    have hidx : c0.length - (2 * ref.val + 1) = 1 := by
      have hclen0 : c.length = c0.length := SimpleGraph.Walk.length_reverse c0
      omega
    rw [hidx]
    simp [c0]
  have hrefl : e.lines ref = l := by
    apply Sum.inr.inj
    exact (e.get_odd ref).symm.trans hrefget
  obtain ⟨i, hiref, hfailure⟩ := compressed_cycle_shortFailure e.points e.lines
    e.from_mem e.to_mem (e.points_ne_of_isCycle hc) e.closed
    (by omega) (e.lines_injective_of_isCycle hc) ref hreflast
  rw [e.first_point, hrefl] at hfailure
  have hqedge : (matchingGraph a l).Adj (Sum.inl (e.points i.castSucc)) (Sum.inr (e.lines i)) :=
    Or.inr hfailure
  have hiedge : s(Sum.inl (e.points i.castSucc), Sum.inr (e.lines i)) ∈ c.edges := by
    apply (c.mk_mem_edges_iff_exists).mpr
    refine ⟨2 * i.val, ?_, ?_⟩
    · have := i.isLt
      omega
    · have heven := e.get_even i.castSucc
      simp only [Fin.val_castSucc] at heven
      rw [heven, e.get_odd i]
  have hiedge0 : s(Sum.inl (e.points i.castSucc), Sum.inr (e.lines i)) ∈ c0.edges := by
    simpa only [c, SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hiedge
  have hsplit : s(Sum.inl (e.points i.castSucc), Sum.inr (e.lines i)) = s(Sum.inl a, Sum.inr l) ∨
      s(Sum.inl (e.points i.castSucc), Sum.inr (e.lines i)) ∈ qG.reverse.edges := by
    simpa only [c0, SimpleGraph.Walk.edges_cons, List.mem_cons] using hiedge0
  rcases hsplit with heq | hmem
  · have hpair : e.points i.castSucc = a ∧ e.lines i = l := by
      simpa only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, false_and, or_false] using heq
    exact hfailure.1 hpair.2
  · have hmemq : s(Sum.inl (e.points i.castSucc), Sum.inr (e.lines i)) ∈ q.edges := by
      simpa only [qG, SimpleGraph.Walk.edges_reverse, List.mem_reverse,
        SimpleGraph.Walk.edges_mapLe_eq_edges] using hmem
    exact (q.adj_of_mem_edges hmemq).2 hqedge

/-- Every actual incidence edge has a constructed matching obstruction. -/
theorem incidence_matching_obstructions [Fintype F] :
    HasMatchingObstructions (incidenceGraph F d) (2 * (d + 2) - 1) := by
  intro u v huv
  cases u with
  | inl a =>
    cases v with
    | inl b => exact False.elim huv
    | inr l =>
      exact ⟨matchingGraph a l, matchingGraph_le huv, matchingGraph_target a l,
        matchingGraph_degree_bound huv, matchingGraph_long huv⟩
  | inr l =>
    cases v with
    | inr m => exact False.elim huv
    | inl a =>
      refine ⟨matchingGraph a l, matchingGraph_le huv, (matchingGraph_target a l).symm,
        matchingGraph_degree_bound huv, ?_⟩
      intro p
      simpa only [SimpleGraph.Walk.length_reverse] using matchingGraph_long huv p.reverse

/-- Theorem 14 for the actual incidence construction. -/
theorem incidence_spanner_eq [Fintype F]
    {H : SimpleGraph (Vertex F d)}
    (hH : IsDegreeFaultSpanner (incidenceGraph F d) H 1 (2 * (d + 2) - 1)) :
    H = incidenceGraph F d := by
  apply eq_of_all_edges_forced hH
  intro u v huv
  obtain ⟨Q, hQG, hQuv, hQdeg, hlong⟩ := incidence_matching_obstructions u v huv
  exact forcing_certificate_of_matching_obstruction huv hQG hQuv hQdeg hlong

/-- Theorem 19 for the actual cloud blowup, without unproved graph hypotheses. -/
theorem incidence_cloud_spanner_eq [Fintype F] (f : ℕ)
    {H : SimpleGraph (Vertex F d × Fin f)}
    (hH : IsDegreeFaultSpanner (cloudGraph (incidenceGraph F d) (Fin f)) H f
      (2 * (d + 2) - 1)) :
    H = cloudGraph (incidenceGraph F d) (Fin f) := by
  apply cloud_spanner_eq incidence_matching_obstructions
  simpa using hH

end DegreeFaultSpanners
