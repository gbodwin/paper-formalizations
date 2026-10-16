import LightSpanners.EdgeSubdivision

/-! Cycle correspondence for one-edge subdivision. -/
namespace LightSpanners
open SimpleGraph
variable {V : Type*}

def subdivisionOldHom (G : SimpleGraph V) (u v : V) :
    G.deleteEdges {s(u,v)} →g subdivideEdge G u v where
  toFun := some
  map_rel' h := deleteEdges_adj.mp h

/-- A walk which avoids the inserted vertex is exactly the image of a walk in
the original graph with the subdivided edge deleted. -/
theorem exists_subdivision_old_walk {G : SimpleGraph V} {u v x y : V}
    (p : (subdivideEdge G u v).Walk (some x) (some y))
    (hp : none ∉ p.support) :
    ∃ q : (G.deleteEdges {s(u,v)}).Walk x y,
      q.map (subdivisionOldHom G u v) = p := by
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    cases p with
    | nil => exact ⟨.nil, rfl⟩
    | @cons _ z _ hxz p =>
      cases z with
      | none => exact (hp (by simp)).elim
      | some z =>
        obtain ⟨q, hq⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p
          (fun h => hp (by simp [h])) rfl
        refine ⟨.cons (deleteEdges_adj.mpr hxz) q, ?_⟩
        simp only [Walk.map_cons, hq]
        rfl

theorem walkWeight_subdivision_old_map {G : SimpleGraph V} {u v x y : V}
    (w : Sym2 V → ℝ) (α β : ℝ) (q : (G.deleteEdges {s(u,v)}).Walk x y) :
    walkWeight (subdivideWeight w u α β) (q.map (subdivisionOldHom G u v)) =
      walkWeight w q := by
  induction q with
  | nil => rfl
  | @cons x z y h q ih =>
    change w s(x,z) + walkWeight (subdivideWeight w u α β)
      (q.map (subdivisionOldHom G u v)) = w s(x,z) + walkWeight w q
    rw [ih]

/-- Cycles avoiding the new vertex correspond to old cycles of exactly the
same weight. The old cycle avoids the subdivided edge. -/
theorem subdivision_cycle_avoiding_new {G : SimpleGraph V} {u v x : V}
    (w : Sym2 V → ℝ) (α β : ℝ)
    (p : (subdivideEdge G u v).Walk (some x) (some x))
    (hp : p.IsCycle) (hn : none ∉ p.support) :
    ∃ q : G.Walk x x, q.IsCycle ∧ s(u,v) ∉ q.edges ∧
      walkWeight w q = walkWeight (subdivideWeight w u α β) p := by
  obtain ⟨q, hq⟩ := exists_subdivision_old_walk p hn
  have hqc : q.IsCycle := (hq.symm ▸ hp).of_map
  refine ⟨q.mapLe (deleteEdges_le _), hqc.mapLe _, ?_, ?_⟩
  · intro he
    have hm := q.edges_subset_edgeSet (by simpa using he)
    simp [edgeSet_deleteEdges] at hm
  · rw [walkWeight_mapLe, ← hq]
    exact (walkWeight_subdivision_old_map (G := G) (u := u) (v := v) w α β q).symm

/-- A cycle based at the inserted degree-two vertex contracts to a cycle of
the original graph. Both replacement edges are used exactly once. -/
theorem subdivision_cycle_at_new {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β : ℝ}
    (hsum : α + β = w s(u,v))
    (p : (subdivideEdge G u v).Walk none none) (hp : p.IsCycle) :
    ∃ (a : V) (q : G.Walk a a), q.IsCycle ∧
      walkWeight w q = walkWeight (subdivideWeight w u α β) p := by
  classical
  cases p with
  | nil => exact (hp.ne_nil rfl).elim
  | @cons _ z _ hnz p =>
    cases z with
    | none => exact hnz.elim
    | some x =>
      cases p with
      | @cons _ z _ hxz p =>
        obtain ⟨y, r, hyn, hr⟩ := p.exists_cons_eq_concat hxz
        rw [hr] at hp ⊢
        cases y with
        | none => exact hyn.elim
        | some y =>
          have hrpath := (Walk.isPath_concat hyn).mp ((Walk.cons_isCycle_iff _ hnz).mp hp).1
          have hxy : x ≠ y := by
            intro heq
            subst y
            have hnd := hp.isTrail.edges_nodup
            simp only [Walk.edges_cons, Walk.edges_concat, List.nodup_cons] at hnd
            exact hnd.1 (by simp [Sym2.eq_swap])
          have hx : x = u ∨ x = v := hnz
          have hy : y = u ∨ y = v := hyn
          have hedge : s(y,x) = s(u,v) := by
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact (hxy rfl).elim
            · exact Sym2.eq_swap
            · rfl
            · exact (hxy rfl).elim
          have hxyG : G.Adj y x := by
            apply (mem_edgeSet G).mp
            rw [hedge]
            exact (mem_edgeSet G).mpr huv
          obtain ⟨q, hq⟩ := exists_subdivision_old_walk r hrpath.2
          have hqpath : q.IsPath := (hq.symm ▸ hrpath.1).of_map
          have hnot : s(y,x) ∉ (q.mapLe (deleteEdges_le _)).edges := by
            intro he
            have hm := q.edges_subset_edgeSet (by simpa using he)
            simp [edgeSet_deleteEdges, hedge] at hm
          refine ⟨y, .cons hxyG (q.mapLe (deleteEdges_le _)),
            (Walk.cons_isCycle_iff _ _).mpr ⟨hqpath.mapLe _, hnot⟩, ?_⟩
          have hw := walkWeight_subdivision_old_map (G := G) (u := u) (v := v) w α β q
          rw [hq] at hw
          change walkWeight (subdivideWeight w u α β) r = walkWeight w q at hw
          simp only [walkWeight_cons, walkWeight_mapLe, Walk.concat_eq_append,
            walkWeight_append, walkWeight_nil, add_zero,
            subdivideWeight_new, subdivideWeight_new', hedge]
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact (hxy rfl).elim
          · simp only [ite_true, ite_eq_right (by simpa using huv.ne.symm)]
            rw [hw, ← hsum]; ring
          · simp only [ite_true, ite_eq_right (by simpa using huv.ne.symm)]
            rw [hw, ← hsum]; ring
          · exact (hxy rfl).elim

/-- Every simple cycle in the subdivided graph contracts to an actual simple
cycle of exactly the same total weight in the original graph. No positivity
assumption is needed for this structural correspondence. -/
theorem subdivision_cycle_contract {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β : ℝ}
    (hsum : α + β = w s(u,v)) {z : Option V}
    (p : (subdivideEdge G u v).Walk z z) (hp : p.IsCycle) :
    ∃ (a : V) (q : G.Walk a a), q.IsCycle ∧
      walkWeight w q = walkWeight (subdivideWeight w u α β) p := by
  classical
  by_cases hn : none ∈ p.support
  · obtain ⟨a, q, hq, hw⟩ := subdivision_cycle_at_new huv w hsum
      (p.rotate none hn) (hp.rotate hn)
    refine ⟨a, q, hq, hw.trans ?_⟩
    exact ((p.rotate_edges none hn).perm.map _).sum_eq
  · cases z with
    | none => exact (hn p.start_mem_support).elim
    | some x =>
      obtain ⟨q, hq, _, hw⟩ := subdivision_cycle_avoiding_new w α β p hp hn
      exact ⟨x, q, hq, hw⟩

end LightSpanners
