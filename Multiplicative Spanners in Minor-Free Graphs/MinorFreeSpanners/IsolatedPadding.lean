import MinorFreeSpanners.DisjointCopies
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! Exact-size padding adds isolated vertices. It preserves edge count,
cycle girth and K_h-minor exclusion for h ≥ 2. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V R : Type*} (G : SimpleGraph V)

def padGraph (R : Type*) : SimpleGraph (V ⊕ R) := G ⊕g (⊥ : SimpleGraph R)

namespace padGraph
variable {G}

/-- The added right-side vertices are genuinely isolated. -/
theorem not_adj_right (r : R) (x : V ⊕ R) : ¬ (padGraph G R).Adj (.inr r) x := by
  cases x <;> simp [padGraph]

theorem walk_from_right {r : R} {x : V ⊕ R}
    (p : (padGraph G R).Walk (.inr r) x) : x = .inr r := by
  cases p with
  | nil => rfl
  | cons h p => exact (not_adj_right _ _ h).elim

/-- On the induced old-vertex set, projection is an injective homomorphism
back to the original graph. -/
noncomputable def oldProjection :
    (padGraph G R).induce (Set.range (Sum.inl : V → V ⊕ R)) →g G where
  toFun x := x.property.choose
  map_rel' := by
    intro x y h
    have hx := x.property.choose_spec
    have hy := y.property.choose_spec
    change (padGraph G R).Adj x.val y.val at h
    rw [← hx,← hy] at h
    exact h

theorem oldProjection_injective : Function.Injective (@oldProjection V R G) := by
  intro x y h
  apply Subtype.ext
  have hx := x.property.choose_spec
  have hy := y.property.choose_spec
  change x.property.choose = y.property.choose at h
  rw [← hx,← hy,h]

/-- A clique model with at least two vertices cannot use an isolated
padding vertex in any branch. -/
theorem minorFree (h : ℕ) (hh : 2 ≤ h) (hG : CliqueMinorFree G h) :
    CliqueMinorFree (padGraph G R) h := by
  classical
  rintro ⟨M⟩
  have hS : ∀ i, M.branch i ⊆ Set.range (Sum.inl : V → V ⊕ R) := by
    intro i x hx
    cases x with
    | inl x => exact ⟨x,rfl⟩
    | inr r =>
      have honly : ∀ y ∈ M.branch i, y = Sum.inr r := by
        intro y hy
        obtain ⟨p,_⟩ := M.connected i _ hx y hy
        exact walk_from_right p
      have hpos : 0 < (Finset.univ.erase i : Finset (Fin h)).card := by simp; omega
      obtain ⟨j,hj⟩ := Finset.card_pos.mp hpos
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      obtain ⟨u,hu,v,hv,huv⟩ := M.adjacent i j (by simpa using hji.symm)
      rw [honly u hu] at huv
      exact (not_adj_right r v huv).elim
  exact hG ⟨(M.induce _ hS).mapHost oldProjection oldProjection_injective⟩

/-- Every cycle is entirely inside the unchanged old-vertex part. -/
theorem girth {k : ℕ} (hG : GirthAbove G k) : GirthAbove (padGraph G R) k := by
  classical
  intro a p hp
  cases a with
  | inr r =>
    cases p with
    | nil => exact (Walk.not_isCycle_nil hp).elim
    | cons h p => exact (not_adj_right _ _ h).elim
  | inl a =>
    have hS : ∀ x ∈ p.support, x ∈ Set.range (Sum.inl : V → V ⊕ R) := by
      intro x hx
      cases x with
      | inl x => exact ⟨x,rfl⟩
      | inr r =>
        exact (not_reachable_sum_inl_inr (G := G) (H := (⊥ : SimpleGraph R)) a r
          (p.takeUntil _ hx).reachable).elim
    let q := p.induce _ hS
    have hq : q.IsCycle := by
      apply Walk.IsCycle.of_map (f := (Embedding.induce _).toHom)
      simpa [q] using hp
    have hlen := hG _ (q.map oldProjection) (hq.map oldProjection_injective)
    have he : q.length = p.length := by
      have hm : (q.map (Embedding.induce _).toHom).length = q.length := Walk.length_map _ _
      exact hm.symm.trans (congrArg (fun w : (padGraph G R).Walk (.inl a) (.inl a) => w.length)
        (p.map_induce hS))
    simpa only [Walk.length_map, he] using hlen

variable [Fintype V] [Fintype R]
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency.types false in
/-- Isolated padding changes the vertex count but adds no edge. -/
theorem edge_count : (padGraph G R).edgeFinset.card = G.edgeFinset.card := by
  have he := Fintype.card_congr (edgeSetSumEquiv (G := G) (H := (⊥ : SimpleGraph R)))
  simp only [Fintype.card_sum, card_edgeSet, edgeFinset_bot, Finset.card_empty,
    add_zero] at he
  convert he using 1
  congr 1

end padGraph
end MinorFreeSpanners
