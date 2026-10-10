import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# A bounded diameter lemma for actual dense graphs

A shortest walk of length at least twelve supplies five vertices at positions
0, 3, 6, 9, and 12 with pairwise disjoint open neighborhoods. Counting those
neighborhoods proves the actual walk witness below. No spacing or neighborhood
certificate is assumed by the diameter theorem.
-/

namespace MinorFreeSpanners

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Every prefix of a shortest walk realizes its own distance. -/
lemma shortest_walk_prefix_dist {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have htake := SimpleGraph.dist_le (p.take i)
  have hdrop := SimpleGraph.dist_le (p.drop i)
  have htriangle := (p.take i).reachable.dist_triangle_left v
  simp only [Walk.take_length, inf_of_le_left hi] at htake
  simp only [Walk.drop_length] at hdrop
  omega

/-- Spacing by three on an actual shortest walk makes the five open
neighborhoods disjoint. A common neighbor would give a two-edge shortcut. -/
lemma shortest_walk_five_neighborhoods_disjoint {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hl : 12 ≤ p.length) :
    Pairwise fun i j : Fin 5 =>
      Disjoint (G.neighborSet (p.getVert (3 * i.val)))
        (G.neighborSet (p.getVert (3 * j.val))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hiz hjz
  have hi : 3 * i.val ≤ p.length := by have := i.isLt; omega
  have hj : 3 * j.val ≤ p.length := by have := j.isLt; omega
  have hdi := shortest_walk_prefix_dist p hp hi
  have hdj := shortest_walk_prefix_dist p hp hj
  have hadj_i : G.Adj (p.getVert (3 * i.val)) z := hiz
  have hadj_j : G.Adj (p.getVert (3 * j.val)) z := hjz
  have hshort_ij : G.dist (p.getVert (3 * i.val)) (p.getVert (3 * j.val)) ≤ 2 := by
    simpa using SimpleGraph.dist_le (Walk.cons hadj_i (Walk.cons hadj_j.symm Walk.nil))
  have hshort_ji : G.dist (p.getVert (3 * j.val)) (p.getVert (3 * i.val)) ≤ 2 := by
    simpa using SimpleGraph.dist_le (Walk.cons hadj_j (Walk.cons hadj_i.symm Walk.nil))
  have htri_ij := (p.take (3 * i.val)).reachable.dist_triangle_left
    (p.getVert (3 * j.val))
  have htri_ji := (p.take (3 * j.val)).reachable.dist_triangle_left
    (p.getVert (3 * i.val))
  have heq : i.val = j.val := by omega
  exact hij (Fin.ext heq)

section Finite

variable [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Five disjoint neighborhoods extracted from a shortest walk account for
at least five times the minimum-degree lower bound. -/
lemma five_mul_le_card_of_long_shortest_walk (δ : ℕ)
    (hdeg : ∀ x : V, δ ≤ G.degree x) {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hl : 12 ≤ p.length) :
    5 * δ ≤ Fintype.card V := by
  classical
  let N : Fin 5 → Type _ := fun i => G.neighborSet (p.getVert (3 * i.val))
  let f : (Σ i : Fin 5, N i) → V := fun x => x.2.val
  have hdisj := shortest_walk_five_neighborhoods_disjoint p hp hl
  have hf : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have heq : i = j := by
      by_contra hne
      apply Set.disjoint_left.mp (hdisj hne) x.property
      have hval : x.val = y.val := hxy
      simpa only [hval] using y.property
    subst j
    have hsub : x = y := Subtype.ext hxy
    subst y
    rfl
  have hcard : Fintype.card (Σ i : Fin 5, N i) ≤ Fintype.card V :=
    Fintype.card_le_of_injective f hf
  calc
    5 * δ = ∑ _i : Fin 5, δ := by simp
    _ ≤ ∑ i : Fin 5, Fintype.card (N i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [N, SimpleGraph.card_neighborSet_eq_degree] using
        hdeg (p.getVert (3 * i.val))
    _ = Fintype.card (Σ i : Fin 5, N i) := Fintype.card_sigma.symm
    _ ≤ Fintype.card V := hcard

/-- For any two reachable vertices, fewer than five times the minimum degree
vertices forces an actual connecting walk of length at most eleven. This
version also covers the empty graph because the endpoints are explicit. -/
theorem exists_short_walk_of_card_lt_five_mul_minDegree (δ : ℕ)
    (hsize : Fintype.card V < 5 * δ) (hdeg : ∀ x : V, δ ≤ G.degree x)
    {u v : V} (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length ≤ 11 := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  refine ⟨p, ?_⟩
  by_contra hlong
  have hl : 12 ≤ p.length := by omega
  have hc := five_mul_le_card_of_long_shortest_walk δ hdeg p hp hl
  omega

/-- The requested finite connected dense-graph diameter bound, with an actual
walk witness. Positivity is stated explicitly although the size bound alone
already implies it. -/
theorem connected_exists_walk_length_le_eleven (δ : ℕ) (_hδ : 0 < δ)
    (hconn : G.Connected) (hdeg : ∀ x : V, δ ≤ G.degree x)
    (hsize : Fintype.card V < 5 * δ) (u v : V) :
    ∃ p : G.Walk u v, p.length ≤ 11 :=
  exists_short_walk_of_card_lt_five_mul_minDegree δ hsize hdeg (hconn u v)

/-- The companion metric statement. -/
theorem connected_dist_le_eleven (δ : ℕ) (hδ : 0 < δ)
    (hconn : G.Connected) (hdeg : ∀ x : V, δ ≤ G.degree x)
    (hsize : Fintype.card V < 5 * δ) (u v : V) :
    G.dist u v ≤ 11 := by
  obtain ⟨p, hp⟩ := connected_exists_walk_length_le_eleven δ hδ hconn hdeg hsize u v
  exact (SimpleGraph.dist_le p).trans hp

end Finite

end MinorFreeSpanners
