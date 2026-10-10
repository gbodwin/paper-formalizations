import GreedyShortcuts.UndirectedGreedy

/-! The ordered-pair potential is exactly twice the unordered-pair potential.
Thus maximizing its drop makes precisely the same greedy choices. -/
namespace GreedyShortcuts.Undirected

open Finset DirectedPaths WeightedPaths
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem out_injective : Function.Injective (Quot.out : Sym2 V → V × V) := by
  intro a b hab
  calc
    a = s(a.out.1,a.out.2) := a.out_eq.symm
    _ = s(b.out.1,b.out.2) := congrArg (fun p : V × V => s(p.1,p.2)) hab
    _ = b := b.out_eq

theorem arcs_sum (H : Finset (Sym2 V)) (f : V × V → ℕ)
    (hf : ∀ s t, f (s,t) = f (t,s))
    (hne : ∀ e ∈ H, e.out.1 ≠ e.out.2) :
    (∑ d ∈ arcs H, f d) = 2 * ∑ e ∈ H, f e.out := by
  classical
  have hd : Disjoint (H.image Quot.out) (H.image (fun e => e.out.swap)) := by
    apply Finset.disjoint_left.mpr
    intro d hd₁ hd₂
    obtain ⟨e,he,hed⟩ := Finset.mem_image.mp hd₁
    obtain ⟨q,hq,hqd⟩ := Finset.mem_image.mp hd₂
    have hprod : e.out = q.out.swap := hed.trans hqd.symm
    have heq : e = q := by
      calc
        e = s(e.out.1,e.out.2) := e.out_eq.symm
        _ = s(q.out.2,q.out.1) := congrArg (fun p : V × V => s(p.1,p.2)) hprod
        _ = q := Sym2.eq_swap.trans q.out_eq
    subst q
    have hfst := congrArg Prod.fst hprod
    exact hne e he hfst
  rw [arcs, Finset.sum_union hd, Finset.sum_image (out_injective.injOn)]
  have hi : Function.Injective (fun e : Sym2 V => e.out.swap) :=
    Prod.swap_injective.comp out_injective
  rw [Finset.sum_image hi.injOn]
  have hs : (∑ e ∈ H, f e.out.swap) = ∑ e ∈ H, f e.out := by
    apply Finset.sum_congr rfl
    intro e he
    exact hf e.out.2 e.out.1
  rw [hs]
  change (∑ e ∈ H, f e.out) + (∑ e ∈ H, f e.out) = _
  omega

theorem arcs_candidates (G : V → V → Prop) (hG : Symmetric G) :
    arcs (candidates G) = DirectedPaths.candidates G := by
  apply Finset.Subset.antisymm (arcs_subset_candidates G hG (Finset.Subset.refl _))
  intro d hd
  exact (mem_arcs _ d.1 d.2).mpr (Finset.mem_image.mpr ⟨d,hd,rfl⟩)

noncomputable def unorderedPotential (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (H : Finset (Sym2 V)) : ℕ :=
  ∑ e ∈ candidates G, GraphGreedy.contribution β
    (hopDistance (augment G (arcs H)) (augmentWeight G w (arcs H)) e.out.1 e.out.2)

theorem potential_eq_twice_unordered (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s) (β : ℕ) (H : Finset (Sym2 V)) :
    potential G w β H = 2 * unorderedPotential G w β H := by
  have hsym : ∀ s t, GraphGreedy.contribution β
      (hopDistance (augment G (arcs H)) (augmentWeight G w (arcs H)) s t) =
      GraphGreedy.contribution β
      (hopDistance (augment G (arcs H)) (augmentWeight G w (arcs H)) t s) := by
    intro s t
    rw [hopDistance_symm _ _ (augment_symmetric G hG H) (augmentWeight_symmetric G w hG hw H) s t]
  have hn : ∀ e ∈ candidates G, e.out.1 ≠ e.out.2 := by
    intro e he
    have ha : e.out ∈ arcs (candidates G) := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)
    rw [arcs_candidates G hG] at ha
    exact ((mem_candidates G e.out).mp ha).1
  unfold potential WeightedGreedy.potential unorderedPotential
  rw [← arcs_candidates G hG]
  exact arcs_sum (candidates G) _ hsym hn

end GreedyShortcuts.Undirected
