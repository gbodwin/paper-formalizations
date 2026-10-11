import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace LinearDistancePreservers.ConnectorPacking
open SimpleGraph

variable {V I : Type*} [Fintype V] [Fintype I] [Nontrivial I]

omit [Fintype V] in
lemma shortest_prefix_dist (G : SimpleGraph V) {a b : V} (p : G.Walk a b)
    (hp : p.length = G.dist a b) {k : ℕ} (hk : k ≤ p.length) :
    G.dist a (p.getVert k) = k := by
  have h := G.length_eq_dist_of_subwalk hp (p.isSubwalk_take k)
  simpa [inf_eq_left.mpr hk] using h.symm

/-- Any connected unweighted gadget faithfully separating the ports of a
natural-length star needs at least the number of vertices in that star.
No tree, bounded degree, private-path, or subdivision hypothesis is used. -/
theorem star_metric_vertex_bound (G : SimpleGraph V) (hconn : G.Connected)
    (port : I → V) (arm : I → ℕ)
    (hsep : ∀ i j, i ≠ j → arm i + arm j ≤ G.dist (port i) (port j)) :
    (∑ i, arm i) + 1 ≤ Fintype.card V := by
  classical
  choose other hother using (fun i : I => exists_ne i)
  choose p hp using (fun i : I => hconn.exists_walk_length_eq_dist (port i) (port (other i)))
  have hlen (i : I) : arm i ≤ (p i).length := by
    have h := hsep i (other i) (hother i).symm
    rw [hp i]
    omega
  let point : (Σ i, Fin (arm i)) → V := fun x => (p x.1).getVert x.2.val
  have hpoint (x : Σ i, Fin (arm i)) : G.dist (port x.1) (point x) = x.2.val := by
    exact shortest_prefix_dist G (p x.1) (hp x.1) (x.2.isLt.le.trans (hlen x.1))
  have hinj : Function.Injective point := by
    rintro ⟨i, k⟩ ⟨j, l⟩ heq
    have hi := hpoint ⟨i,k⟩
    have hj := hpoint ⟨j,l⟩
    change G.dist (port i) (point ⟨i,k⟩) = k.val at hi
    change G.dist (port j) (point ⟨j,l⟩) = l.val at hj
    have hij : i = j := by
      by_contra hne
      have hs := hsep i j hne
      have ht := hconn.dist_triangle (u := port i) (v := point ⟨i,k⟩) (w := port j)
      have hr : G.dist (point ⟨i,k⟩) (port j) = l.val := by
        rw [heq, G.dist_comm]
        exact hj
      rw [hi, hr] at ht
      have hk := k.isLt
      have hl := l.isLt
      omega
    subst j
    have hkl : k = l := by
      apply Fin.ext
      exact hi.symm.trans ((congrArg (G.dist (port i)) heq).trans hj)
    subst l
    rfl
  let i₀ : I := Classical.choice inferInstance
  let middle : V := (p i₀).getVert (arm i₀)
  have hm : G.dist (port i₀) middle = arm i₀ :=
    shortest_prefix_dist G (p i₀) (hp i₀) (hlen i₀)
  have hfar (i : I) : arm i ≤ G.dist (port i) middle := by
    by_cases hi : i = i₀
    · subst i
      exact hm.ge
    · have hs := hsep i i₀ hi
      have ht := hconn.dist_triangle (u := port i) (v := middle) (w := port i₀)
      have hr : G.dist middle (port i₀) = arm i₀ := by rw [G.dist_comm]; exact hm
      rw [hr] at ht
      omega
  have hne (x : Σ i, Fin (arm i)) : point x ≠ middle := by
    intro hx
    have hf := hfar x.1
    have hx' := hpoint x
    rw [hx] at hx'
    have hlt := x.2.isLt
    omega
  let embed : Option (Σ i, Fin (arm i)) → V := fun x => x.elim middle point
  have hembed : Function.Injective embed := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact False.elim (hne y hxy.symm)
    | some x =>
      cases y with
      | none => exact False.elim (hne x hxy)
      | some y => exact congrArg some (hinj hxy)
  have hc := Fintype.card_le_of_injective embed hembed
  simpa [Fintype.card_sigma] using hc

/-- The same obstruction stated in the graph's native extended distance. -/
theorem star_metric_vertex_bound_edist (G : SimpleGraph V) (hconn : G.Connected)
    (port : I → V) (arm : I → ℕ)
    (hsep : ∀ i j, i ≠ j → (arm i + arm j : ℕ) ≤ G.edist (port i) (port j)) :
    (∑ i, arm i) + 1 ≤ Fintype.card V := by
  apply star_metric_vertex_bound G hconn port arm
  intro i j hij
  have h := hsep i j hij
  rw [← (hconn (port i) (port j)).coe_dist_eq_edist] at h
  exact_mod_cast h

/-- Even arbitrary shared high-degree gadgets cannot compress the uniform
D-port, arm-length-L star metric below its private-subdivision vertex count. -/
theorem uniform_star_vertex_bound (G : SimpleGraph V) (hconn : G.Connected)
    (D L : ℕ) (hD : 2 ≤ D) (port : Fin D → V)
    (hsep : ∀ i j, i ≠ j → (2*L : ℕ) ≤ G.edist (port i) (port j)) :
    D*L + 1 ≤ Fintype.card V := by
  let : Nontrivial (Fin D) := Fin.nontrivial_iff_two_le.mpr hD
  have h := star_metric_vertex_bound_edist G hconn port (fun _ => L) (by
    intro i j hij
    simpa [two_mul] using hsep i j hij)
  simpa using h

end LinearDistancePreservers.ConnectorPacking
