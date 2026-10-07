import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! The deterministic induced-matching argument in Lemma 6. The lazy tree and
its shortest-path depth labels are supplied explicitly. This module does not
assume the induced-matching conclusion and does not construct the lazy tree. -/
namespace LinearDistancePreservers

structure LazyEdges (V : Type*) (G : V → V → Prop) (depth : V → ℕ) where
  symmetric : ∀ u v, G u v → G v u
  edge : V → V → Prop
  adjacent : ∀ u v, edge u v → G u v
  increases : ∀ u v, edge u v → depth v = depth u + 1
  child_unique : ∀ u v w, edge u v → edge u w → v = w
  parent_unique : ∀ u v w, edge u w → edge v w → u = v
  lazy : ∀ u v u' v', edge u v → edge u' v' → u ≠ u' →
    depth u = depth u' → ¬ G u v'
  lipschitz : ∀ u v, G u v → depth u ≤ depth v + 1 ∧ depth v ≤ depth u + 1

namespace LazyEdges
variable {V : Type*} {G : V → V → Prop} {depth : V → ℕ}

def Cut (color : V → Bool) (u v : V) : Prop := G u v ∧ color u ≠ color v

def InClass (T : LazyEdges V G depth) (color : V → Bool) (r : Fin 3) (e : V × V) : Prop :=
  T.edge e.1 e.2 ∧ color e.1 = false ∧ color e.2 = true ∧ depth e.1 % 3 = r.val

/-- Distinct selected edges have disjoint endpoint sets and no cross edges
in the retained cut graph; each residue class is an induced matching. -/
theorem class_is_induced_matching (T : LazyEdges V G depth) (color : V → Bool)
    (r : Fin 3) {u v u' v' : V}
    (he : T.InClass color r (u,v)) (hf : T.InClass color r (u',v'))
    (hne : (u,v) ≠ (u',v')) :
    Cut (G := G) color u v ∧ Cut (G := G) color u' v' ∧
    u ≠ u' ∧ v ≠ v' ∧ u ≠ v' ∧ v ≠ u' ∧
    ¬ Cut (G := G) color u u' ∧ ¬ Cut (G := G) color u v' ∧
    ¬ Cut (G := G) color v u' ∧ ¬ Cut (G := G) color v v' := by
  rcases he with ⟨he,huc,hvc,hur⟩
  rcases hf with ⟨hf,hu'c,hv'c,hu'r⟩
  dsimp only at *
  have huu : u ≠ u' := by
    intro h
    subst u'
    exact hne (Prod.ext rfl (T.child_unique _ _ _ he hf))
  have hvv : v ≠ v' := by
    intro h
    subst v'
    exact hne (Prod.ext (T.parent_unique _ _ _ he hf) rfl)
  have huv : u ≠ v' := by intro h; rw [h,hv'c] at huc; cases huc
  have hvu : v ≠ u' := by intro h; rw [h,hu'c] at hvc; cases hvc
  have du := T.increases _ _ he
  have du' := T.increases _ _ hf
  have hcross : ¬ G u v' := by
    intro h
    have hd := T.lipschitz _ _ h
    have hsame : depth u = depth u' := by omega
    exact T.lazy _ _ _ _ he hf huu hsame h
  have hcross' : ¬ G v u' := by
    intro h
    have hd := T.lipschitz _ _ h
    have hsame : depth u' = depth u := by omega
    have hgv : ¬ G u' v := T.lazy _ _ _ _ hf he (Ne.symm huu) hsame
    exact hgv (T.symmetric _ _ h)
  refine ⟨⟨T.adjacent _ _ he,by simp [huc,hvc]⟩,
    ⟨T.adjacent _ _ hf,by simp [hu'c,hv'c]⟩,huu,hvv,huv,hvu,?_,?_,?_,?_⟩
  · simp [Cut,huc,hu'c]
  · exact fun h => hcross h.1
  · exact fun h => hcross' h.1
  · simp [Cut,hvc,hv'c]

end LazyEdges
end LinearDistancePreservers
