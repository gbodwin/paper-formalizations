import LightSpanners.SubdivisionCycles

/-! Weighted-girth lower bounds survive arbitrary one-edge subdivision with
nonnegative replacement weights. Draft, not yet checked or published. -/
namespace LightSpanners
open SimpleGraph
variable {V : Type*}

@[simp] theorem subdivideWeight_map_some (w : Sym2 V → ℝ) (u : V) (α β : ℝ)
    (e : Sym2 V) : subdivideWeight w u α β (Sym2.map some e) = w e := by
  induction e using Sym2.inductionOn with
  | hf x y => rfl

theorem subdivision_girth_avoiding_new {G : SimpleGraph V} {u v x : V}
    (w : Sym2 V → ℝ) (α β g : ℝ) (hG : WeightedGirthAbove G w g)
    (p : (subdivideEdge G u v).Walk (some x) (some x))
    (hp : p.IsCycle) (hn : none ∉ p.support) :
    ∀ e ∈ p.edges, g * subdivideWeight w u α β e <
      walkWeight (subdivideWeight w u α β) p := by
  obtain ⟨q, hq⟩ := exists_subdivision_old_walk p hn
  have hqc : q.IsCycle := (hq.symm ▸ hp).of_map
  have hw : walkWeight (subdivideWeight w u α β) p = walkWeight w q := by
    rw [← hq]
    exact walkWeight_subdivision_old_map (G := G) (u := u) (v := v) w α β q
  intro e he
  rw [← hq, Walk.edges_map] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  have H := hG x (q.mapLe (deleteEdges_le _)) (hqc.mapLe _) d (by simpa using hd)
  simpa only [walkWeight_mapLe, subdivideWeight_map_some, hw] using H

theorem subdivision_girth_at_new {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β g : ℝ}
    (hsum : α + β = w s(u,v)) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hg : 0 ≤ g) (hG : WeightedGirthAbove G w g)
    (p : (subdivideEdge G u v).Walk none none) (hp : p.IsCycle) :
    ∀ e ∈ p.edges, g * subdivideWeight w u α β e <
      walkWeight (subdivideWeight w u α β) p := by
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
          let c : G.Walk y y := .cons hxyG (q.mapLe (deleteEdges_le _))
          have hc : c.IsCycle := (Walk.cons_isCycle_iff _ _).mpr ⟨hqpath.mapLe _, hnot⟩
          have hw : walkWeight (subdivideWeight w u α β) r = walkWeight w q := by
            rw [← hq]
            exact walkWeight_subdivision_old_map (G := G) (u := u) (v := v) w α β q
          have hcweight : walkWeight w c =
              walkWeight (subdivideWeight w u α β) (.cons hnz (r.concat hyn)) := by
            simp only [c, walkWeight_cons, walkWeight_mapLe, Walk.concat_eq_append,
              walkWeight_append, walkWeight_nil, add_zero, subdivideWeight_new,
              subdivideWeight_new', hedge]
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact (hxy rfl).elim
            · simp only [ite_true, ite_eq_right (by simpa using huv.ne.symm)]
              rw [hw, ← hsum]; ring
            · simp only [ite_true, ite_eq_right (by simpa using huv.ne.symm)]
              rw [hw, ← hsum]; ring
            · exact (hxy rfl).elim
          have Huv : g * w s(u,v) < walkWeight w c := hG y c hc _ (by simp [c, hedge])
          have hpiece : ∀ a : V, subdivideWeight w u α β s(none, some a) ≤ w s(u,v) := by
            intro a
            simp only [subdivideWeight_new]
            split_ifs <;> linarith only [hsum, hα, hβ]
          intro e he
          rw [← hcweight]
          simp only [Walk.edges_cons, Walk.edges_concat, List.mem_cons,
            List.mem_append, List.mem_singleton] at he
          rcases he with rfl | he | rfl
          · exact (mul_le_mul_of_nonneg_left (hpiece x) hg).trans_lt Huv
          · rw [← hq, Walk.edges_map] at he
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
            simpa only [subdivideWeight_map_some] using
              hG y c hc d (by simp [c, hd])
          · have H := (mul_le_mul_of_nonneg_left (hpiece y) hg).trans_lt Huv
            simpa only [Sym2.eq_swap] using H

/-- Subdividing an edge into two nonnegative pieces cannot decrease weighted
cycle girth. This is a lower-bound transfer, not equality of normalized girth. -/
theorem WeightedGirthAbove.subdivideEdge {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β g : ℝ}
    (hsum : α + β = w s(u,v)) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hg : 0 ≤ g) (hG : WeightedGirthAbove G w g) :
    WeightedGirthAbove (subdivideEdge G u v) (subdivideWeight w u α β) g := by
  classical
  intro z p hp e he
  by_cases hn : none ∈ p.support
  · have H := subdivision_girth_at_new huv w hsum hα hβ hg hG
      (p.rotate none hn) (hp.rotate hn) e ((p.rotate_edges none hn).perm.mem_iff.mpr he)
    have hw : walkWeight (subdivideWeight w u α β) (p.rotate none hn) =
        walkWeight (subdivideWeight w u α β) p := ((p.rotate_edges none hn).perm.map _).sum_eq
    exact H.trans_eq hw
  · cases z with
    | none => exact (hn p.start_mem_support).elim
    | some x => exact subdivision_girth_avoiding_new w α β g hG p hp hn e he

end LightSpanners
