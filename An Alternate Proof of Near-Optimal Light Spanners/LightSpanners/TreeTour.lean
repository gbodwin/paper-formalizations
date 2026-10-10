import LightSpanners.Girth
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace LightSpanners
open SimpleGraph
universe u

/-- Leaf insertion constructs a closed spanning walk of optimal tree-tour length. -/
theorem exists_tree_tour_aux (k : ℕ) :
    ∀ (V : Type u) [Fintype V] (T : SimpleGraph V), T.IsTree → Fintype.card V ≤ k →
      ∃ r : V, ∃ p : T.Walk r r,
        p.length = 2 * (Fintype.card V - 1) ∧ ∀ v : V, v ∈ p.support := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro V _ T hT hk
    let : Nonempty V := hT.connected.nonempty
    by_cases hsmall : Fintype.card V ≤ 1
    · let : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hsmall
      let r : V := Classical.choice inferInstance
      refine ⟨r, .nil, ?_, ?_⟩
      · simp only [Walk.length_nil]
        omega
      · intro v
        simpa only [Subsingleton.elim v r] using (Walk.start_mem_support (Walk.nil : T.Walk r r))
    · let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨a, hva, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
      have hav : a ≠ v := hva.ne.symm
      let W := ↥(({v} : Set V)ᶜ)
      let S : SimpleGraph W := T.induce ({v}ᶜ)
      have hS : S.IsTree := ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
        hT.isAcyclic.induce _⟩
      have hc : Fintype.card W = Fintype.card V - 1 := by
        change Fintype.card ↥(({v} : Set V)ᶜ) = Fintype.card V - 1
        rw [Fintype.card_compl_set]
        simp
      obtain ⟨r, p, hlen, hcover⟩ := ih (Fintype.card W) (by omega) W S hS le_rfl
      let f : S →g T := { toFun := Subtype.val, map_rel' := fun h => h }
      let q := p.map f
      have hcoverq : ∀ x : V, x ≠ v → x ∈ q.support := by
        intro x hx
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨⟨x, hx⟩, hcover ⟨x, hx⟩, rfl⟩
      let c := q.rotate a (hcoverq a hav)
      let out := (Walk.cons hva.symm (Walk.cons hva .nil)).append c
      refine ⟨a, out, ?_, ?_⟩
      · simp only [out, Walk.length_append, Walk.length_cons, Walk.length_nil,
          c, Walk.length_rotate, q, Walk.length_map, hlen]
        omega
      · intro x
        by_cases hx : x = v
        · subst x
          exact (Walk.support_subset_support_append_left _ _)
            (by simp only [Walk.support_cons, Walk.support_nil, List.mem_cons]; tauto)
        · apply Walk.support_subset_support_append_right
          exact (q.mem_support_rotate_iff a _).mpr (hcoverq x hx)

/-- Every finite tree has an actual closed walk covering all vertices with
exactly `2(n-1)` edge traversals. This supplies the vertex budget for the
Euler-tour unfolding in Lemma 3.5; no tour is assumed as input. -/
theorem exists_tree_tour {V : Type u} [Fintype V] {T : SimpleGraph V} (hT : T.IsTree) :
    ∃ r : V, ∃ p : T.Walk r r,
      p.length = 2 * (Fintype.card V - 1) ∧ ∀ v : V, v ∈ p.support :=
  exists_tree_tour_aux (Fintype.card V) V T hT le_rfl

/-- Every finite simple cycle uses at most the number of vertices. -/
theorem cycle_length_le_card {V : Type u} [Fintype V] {G : SimpleGraph V}
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) : p.length ≤ Fintype.card V := by
  have h := hp.isPath_tail.length_lt
  have hlen := hp.three_le_length
  simp only [Walk.length_tail] at h
  omega

theorem nonforest_exists_cycle {V : Type u} {G : SimpleGraph V} (hnon : ¬ G.IsAcyclic) :
    ∃ a : V, ∃ p : G.Walk a a, p.IsCycle := by
  classical
  simpa only [SimpleGraph.IsAcyclic, not_forall, not_not] using hnon

/-- The non-forest hypothesis also supplies the small-order side condition. -/
theorem nonforest_three_le_card {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hnon : ¬ G.IsAcyclic) : 3 ≤ Fintype.card V := by
  obtain ⟨a, p, hp⟩ := nonforest_exists_cycle hnon
  exact hp.three_le_length.trans (cycle_length_le_card p hp)

/-- In a positive-weight non-forest, a strict weighted-girth threshold is
strictly below the vertex count. This bounds the new position cycle. -/
theorem WeightedGirthAbove.threshold_lt_card_of_nonforest
    {V : Type u} [Fintype V] {G : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ}
    (hG : WeightedGirthAbove G w g) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hnon : ¬ G.IsAcyclic) : g < Fintype.card V := by
  obtain ⟨a, p, hp⟩ := nonforest_exists_cycle hnon
  obtain ⟨e, he, hmax⟩ := exists_max_cycle_edge w p hp
  have hpos := hw e (p.edges_subset_edgeSet he)
  have hbound := hG a p hp e he
  have hlen := walkWeight_le_length_mul p w (w e) hmax
  have hlt : g < p.length :=
    (mul_lt_mul_iff_of_pos_right hpos).mp (hbound.trans_le hlen)
  exact hlt.trans_le (by exact_mod_cast cycle_length_le_card p hp)

end LightSpanners
