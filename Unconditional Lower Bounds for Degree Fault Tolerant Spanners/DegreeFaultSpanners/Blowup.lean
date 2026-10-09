import DegreeFaultSpanners.FaultSpanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Cloud blowups and their fault certificates

Definitions 15 and 17 and Lemma 18 of arXiv:2607.07576v1.
The base obstruction must certify that the fault set *together with* the
protected edge is a matching. The weaker assertion that the faults alone
are a matching would not suffice for the lifted degree bound.
-/

namespace DegreeFaultSpanners

open SimpleGraph
open scoped BigOperators

variable {V C : Type*}

/-- Replace every base vertex by a cloud indexed by `C`, and each edge by a biclique. -/
def cloudGraph (G : SimpleGraph V) (C : Type*) : SimpleGraph (V × C) :=
  G.comap Prod.fst

@[simp] theorem cloudGraph_adj (G : SimpleGraph V) (x y : V × C) :
    (cloudGraph G C).Adj x y ↔ G.Adj x.1 y.1 := Iff.rfl

/-- A lifted vertex is adjacent to all copies of every base neighbor. -/
theorem cloudGraph_neighborSet (G : SimpleGraph V) (x : V × C) :
    (cloudGraph G C).neighborSet x = G.neighborSet x.1 ×ˢ (Set.univ : Set C) := by
  ext y
  simp [cloudGraph, SimpleGraph.neighborSet_comap]

@[simp] theorem cloudGraph_vertex_count [Fintype V] [Fintype C] :
    Fintype.card (V × C) = Fintype.card V * Fintype.card C := Fintype.card_prod _ _

/-- Exact multiplication of every vertex degree by the cloud size. -/
theorem cloudGraph_neighbor_count [Fintype V] [Fintype C]
    (G : SimpleGraph V) (x : V × C) :
    ((cloudGraph G C).neighborSet x).ncard =
      (G.neighborSet x.1).ncard * Fintype.card C := by
  rw [cloudGraph_neighborSet, Set.ncard_prod]
  simp [Nat.card_eq_fintype_card]

/-- Exact multiplication of the undirected edge count by the square cloud size. -/
theorem cloudGraph_edge_count [Fintype V] [Fintype C] (G : SimpleGraph V) :
    Nat.card (cloudGraph G C).edgeSet = Fintype.card C ^ 2 * Nat.card G.edgeSet := by
  classical
  let B := cloudGraph G C
  have hdegree (x : V × C) : B.degree x = G.degree x.1 * Fintype.card C := by
    simpa only [SimpleGraph.ncard_neighborSet] using cloudGraph_neighbor_count G x
  have hsum : ∑ x : V × C, B.degree x =
      Fintype.card C ^ 2 * (∑ v : V, G.degree v) := by
    simp_rw [hdegree]
    rw [Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    change (∑ _ : C, G.degree v * Fintype.card C) = Fintype.card C ^ 2 * G.degree v
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul, Nat.cast_id]
    ring
  have hB := B.sum_degrees_eq_twice_card_edges
  have hG := G.sum_degrees_eq_twice_card_edges
  have hcardB : B.edgeFinset.card = Nat.card B.edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  have hcardG : G.edgeFinset.card = Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  rw [hcardB] at hB
  rw [hcardG] at hG
  have heq : 2 * Nat.card B.edgeSet = 2 * (Fintype.card C ^ 2 * Nat.card G.edgeSet) := by
    rw [← hB, hsum, hG]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) heq

/-- Any base degree bound lifts by the cloud size. -/
theorem cloudGraph_degree_bound [Fintype V] [Fintype C]
    {G : SimpleGraph V} {d : ℕ} (h : HasDegreeBound G d) :
    HasDegreeBound (cloudGraph G C) (d * Fintype.card C) := by
  intro x
  rw [cloudGraph_neighbor_count]
  exact Nat.mul_le_mul_right _ (h x.1)

/-- A subgraph inherits any pointwise fault-degree bound. -/
theorem HasDegreeBound.mono_graph [Fintype V] {G H : SimpleGraph V} {d : ℕ}
    (h : HasDegreeBound G d) (hHG : H ≤ G) : HasDegreeBound H d := by
  intro v
  exact (Set.ncard_le_ncard (fun _ hv => hHG hv)).trans (h v)

/-- The lifted fault graph exempts exactly the protected lifted edge. -/
def liftedFault (Q : SimpleGraph V) (x y : V × C) : SimpleGraph (V × C) :=
  (cloudGraph Q C).deleteEdges {s(x, y)}

/-- Lemma 18: lifting a matching and exempting one edge has degree at most the cloud size. -/
theorem liftedFault_degree_bound [Fintype V] [Fintype C]
    {Q : SimpleGraph V} (hQ : HasDegreeBound Q 1) (x y : V × C) :
    HasDegreeBound (liftedFault Q x y) (Fintype.card C) := by
  have h := cloudGraph_degree_bound (C := C) hQ
  simp only [one_mul] at h
  exact h.mono_graph ((cloudGraph Q C).deleteEdges_le _)

@[simp] theorem liftedFault_not_target (Q : SimpleGraph V) (x y : V × C) :
    ¬ (liftedFault Q x y).Adj x y := by
  simp [liftedFault]

/-- A projected path avoiding lifted faults and the exempt edge avoids the entire base matching. -/
def survivingProjection (G Q : SimpleGraph V) (x y : V × C) :
    ((cloudGraph G C \ liftedFault Q x y).deleteEdges {s(x, y)}) →g (G \ Q) where
  toFun := Prod.fst
  map_rel' := by
    intro a b hab
    have hd := SimpleGraph.deleteEdges_adj.mp hab
    have hG : G.Adj a.1 b.1 := hd.1.1
    refine ⟨hG, ?_⟩
    intro hQ
    apply hd.1.2
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hQ, hd.2⟩

/-- Generic cloud lifting of a matching obstruction.
Here `Q` is the base fault set with the target edge already adjoined. -/
theorem cloud_forcing_certificate [Fintype V] [Fintype C]
    {G Q : SimpleGraph V} {u v : V} {t : ℕ}
    (huv : G.Adj u v) (hQG : Q ≤ G) (hQuv : Q.Adj u v)
    (hQdeg : HasDegreeBound Q 1)
    (hlong : ∀ p : (G \ Q).Walk u v, t < p.length)
    (i j : C) :
    EdgeForcingCertificate (cloudGraph G C) (Fintype.card C) t (u, i) (v, j) := by
  refine ⟨huv, liftedFault Q (u, i) (v, j), ?_, liftedFault_not_target _ _ _, ?_⟩
  · refine ⟨?_, liftedFault_degree_bound hQdeg _ _⟩
    intro a b hab
    exact hQG (SimpleGraph.deleteEdges_adj.mp hab).1
  · intro p
    have h := hlong (p.map (survivingProjection G Q (u, i) (v, j)))
    have hlen := SimpleGraph.Walk.length_map (survivingProjection G Q (u, i) (v, j)) p
    exact hlen ▸ h

/-- The geometric base graph must construct one matching obstruction per edge. -/
def HasMatchingObstructions [Fintype V] (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∀ u v, G.Adj u v → ∃ Q : SimpleGraph V,
    Q ≤ G ∧ Q.Adj u v ∧ HasDegreeBound Q 1 ∧
      ∀ p : (G \ Q).Walk u v, t < p.length

/-- The full generic cloud-lifting step of Theorem 19.
The incidence-specific construction of the matching obstructions is separate. -/
theorem cloud_spanner_eq [Fintype V] [Fintype C]
    {G : SimpleGraph V} {t : ℕ} (hG : HasMatchingObstructions G t)
    {H : SimpleGraph (V × C)}
    (hH : IsDegreeFaultSpanner (cloudGraph G C) H (Fintype.card C) t) :
    H = cloudGraph G C := by
  apply eq_of_all_edges_forced hH
  intro x y hxy
  obtain ⟨Q, hQG, hQxy, hQdeg, hlong⟩ := hG x.1 y.1 hxy
  exact cloud_forcing_certificate (G := G) (Q := Q) (u := x.1) (v := y.1)
    hxy hQG hQxy hQdeg hlong x.2 y.2

end DegreeFaultSpanners
