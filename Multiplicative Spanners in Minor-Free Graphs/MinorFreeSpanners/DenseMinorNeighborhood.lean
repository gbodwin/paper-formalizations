import MinorFreeSpanners.MinimalDenseMinor
import MinorFreeSpanners.EdgeContractionCount
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The deterministic first step of the Alon–Krivelevich–Sudakov proof.
All minors are actual branch-set models. Integer density, nonempty targets,
parallel-edge suppression, and the exact contraction loss are explicit. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*}
attribute [local instance] Classical.propDecidable

theorem MinimalDenseFiniteMinor.two_le_vertices {G : SimpleGraph V} {d n : ℕ}
    (M : MinimalDenseFiniteMinor G d n) (hd : 0 < d) : 2 ≤ n := by
  classical
  have hne : M.graph ≠ ⊥ := by
    intro h
    have hm : d*n ≤ M.graph.edgeFinset.card := M.density
    have hz : M.graph.edgeFinset.card = 0 :=
      Finset.card_eq_zero.mpr (SimpleGraph.edgeFinset_eq_empty.mpr h)
    rw [hz] at hm
    exact (Nat.not_le_of_gt (Nat.mul_pos hd M.positive_vertices)) hm
  obtain ⟨u,v,huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  by_contra h
  exact huv.ne (Fin.ext (by omega))

/-- Deleting any one vertex of the minimal graph loses more than d edges. -/
theorem MinimalDenseFiniteMinor.degree_gt {G : SimpleGraph V} {d n : ℕ}
    (M : MinimalDenseFiniteMinor G d n) (hd : 0 < d) (u : Fin n) :
    d < M.graph.degree u := by
  classical
  have hn := M.two_le_vertices hd
  let H := M.graph.comap (Subtype.val : {x : Fin n // x ≠ u} → Fin n)
  have hverts : Fintype.card {x : Fin n // x ≠ u} = n-1 := by
    simpa using contractEdge_vertex_card (V := Fin n) u
  have hcard : H.edgeFinset.card = M.graph.edgeFinset.card - M.graph.degree u := by
    exact (M.graph.card_edgeFinset_induce_compl_singleton u).trans
      (M.graph.card_edgeFinset_deleteIncidenceSet u)
  let N : MinorModel H G :=
    (MinorModel.ofEmbedding H M.graph (Function.Embedding.subtype _) (fun _ _ h => h)).comp M.model
  have hpos : 0 < Fintype.card {x : Fin n // x ≠ u} := by rw [hverts]; omega
  have hsmall : Fintype.card {x : Fin n // x ≠ u}+H.edgeFinset.card <
      n+M.graph.edgeFinset.card := by rw [hverts,hcard]; omega
  have hs : H.edgeFinset.card < d*Fintype.card {x : Fin n // x ≠ u} :=
    M.smaller_minor_sparse H N hpos hsmall
  rw [hverts,hcard] at hs
  have heq : M.graph.edgeFinset.card = d*n := M.edge_count_eq
  have hdeg := M.graph.degree_le_card_edgeFinset u
  have hprod : d*n = d*(n-1)+d := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    simp [Nat.mul_add]
  omega

/-- Each edge of the minimal graph lies in at least d actual triangles. -/
theorem MinimalDenseFiniteMinor.common_neighbors_ge {G : SimpleGraph V} {d n : ℕ}
    (M : MinimalDenseFiniteMinor G d n) (hd : 0 < d) {u v : Fin n}
    (huv : M.graph.Adj u v) :
    d ≤ Fintype.card (M.graph.commonNeighbors u v) := by
  classical
  have hn := M.two_le_vertices hd
  let H := contractEdge M.graph u v
  let N : MinorModel H G := (contractEdgeModel M.graph u v huv).comp M.model
  have hverts : Fintype.card {x : Fin n // x ≠ v} = n-1 := by
    simpa using contractEdge_vertex_card (V := Fin n) v
  have hcount := contractEdge_edge_count M.graph u v huv
  change H.edgeFinset.card + 1 + Fintype.card (M.graph.commonNeighbors u v) =
    M.graph.edgeFinset.card at hcount
  have hpos : 0 < Fintype.card {x : Fin n // x ≠ v} := by rw [hverts]; omega
  have hsmall : Fintype.card {x : Fin n // x ≠ v}+H.edgeFinset.card <
      n+M.graph.edgeFinset.card := by rw [hverts]; omega
  have hs : H.edgeFinset.card < d*Fintype.card {x : Fin n // x ≠ v} :=
    M.smaller_minor_sparse H N hpos hsmall
  rw [hverts] at hs
  have heq : M.graph.edgeFinset.card = d*n := M.edge_count_eq
  have hprod : d*n = d*(n-1)+d := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    simp [Nat.mul_add]
  omega

/-- The exact integer density gives an actual vertex of degree at most 2d. -/
theorem MinimalDenseFiniteMinor.exists_degree_le {G : SimpleGraph V} {d n : ℕ}
    (M : MinimalDenseFiniteMinor G d n) : ∃ u, M.graph.degree u ≤ 2*d := by
  classical
  by_contra h
  have hforall : ∀ u, 2*d+1 ≤ M.graph.degree u := by
    intro u
    have hu : ¬ M.graph.degree u ≤ 2*d := fun hh => h ⟨u,hh⟩
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hforall u)
  have heq := M.graph.sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  rw [heq,M.edge_count_eq] at hsum
  have hp := M.positive_vertices
  nlinarith

/-- Neighborhood induction turns common-neighbor cardinality into degree,
via an explicit equivalence of actual neighbor subtypes. -/
theorem induced_neighborhood_degree [Fintype V] (G : SimpleGraph V)
    (v : V) (x : G.neighborSet v) :
    (G.induce (G.neighborSet v)).degree x = Fintype.card (G.commonNeighbors v x.val) := by
  classical
  rw [← card_neighborSet_eq_degree]
  apply Fintype.card_congr
  exact {
    toFun := fun y => ⟨y.val.val,⟨y.val.property,y.property⟩⟩
    invFun := fun y => ⟨⟨y.val,y.property.1⟩,y.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- An actual graph of integer density at least d has a genuine minor
neighborhood with at most 2d vertices and minimum degree at least d. -/
theorem exists_dense_minor_neighborhood [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (hd : 0 < d) (hn : 0 < Fintype.card V)
    (hG : d*Fintype.card V ≤ G.edgeFinset.card) :
    ∃ n, ∃ (M : MinimalDenseFiniteMinor G d n) (v : Fin n),
      Nonempty (MinorModel (M.graph.induce (M.graph.neighborSet v)) G) ∧
      0 < Fintype.card (M.graph.neighborSet v) ∧
      Fintype.card (M.graph.neighborSet v) ≤ 2*d ∧
      ∀ x : M.graph.neighborSet v, d ≤ (M.graph.induce (M.graph.neighborSet v)).degree x := by
  classical
  obtain ⟨n,⟨M⟩⟩ := exists_minimal_dense_minor G d hn hG
  obtain ⟨v,hv⟩ := M.exists_degree_le
  refine ⟨n,M,v,?_,?_,?_,?_⟩
  · exact ⟨(MinorModel.ofEmbedding _ M.graph (Function.Embedding.subtype _)
      (fun _ _ h => h)).comp M.model⟩
  · rw [card_neighborSet_eq_degree]
    exact lt_trans hd (M.degree_gt hd v)
  · simpa only [card_neighborSet_eq_degree] using hv
  · intro x
    rw [induced_neighborhood_degree]
    exact M.common_neighbors_ge hd x.property

end MinorFreeSpanners
