import LightEFTSpanners.ParallelSubdivision
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
variable {V I : Type*} [Fintype V] [Fintype I] (C : SimpleGraph V)
attribute [local instance] Classical.propDecidable

/-- The neighbors of an original vertex are exactly its incident base edges,
each paired with a copy index. -/
noncomputable def coreNeighborEquiv (a : V) :
    (graph (I:=I) C).neighborSet (Sum.inl a) ≃
      ({d : C.edgeSet // a∈(d:Sym2 V)} × I) where
  toFun x := match x with
    | ⟨Sum.inl _,h⟩ => False.elim h
    | ⟨Sum.inr z,h⟩ => (⟨z.1,h⟩,z.2)
  invFun z := ⟨Sum.inr (z.1.1,z.2),z.1.2⟩
  left_inv x := by
    rcases x with ⟨x,h⟩
    cases x with
    | inl b => exact False.elim h
    | inr z => rfl
  right_inv z := by rfl

/-- Actual core degrees are multiples of the number of subdivision copies. -/
theorem core_degree (a : V) :
    (graph (I:=I) C).degree (Sum.inl a) =
      Fintype.card {d : C.edgeSet // a∈(d:Sym2 V)} * Fintype.card I := by
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (coreNeighborEquiv (I:=I) C a)]
  exact Fintype.card_prod _ _

/-- Each new branch vertex has exactly the two distinct endpoints of its
actual base edge as neighbors. -/
theorem branch_degree (a b : V) (hab : C.Adj a b) (j : I) :
    (graph (I:=I) C).degree
      (Sum.inr (⟨s(a,b),(mem_edgeSet C).mpr hab⟩,j)) = 2 := by
  classical
  let d : C.edgeSet := ⟨s(a,b),(mem_edgeSet C).mpr hab⟩
  have hn : (graph (I:=I) C).neighborFinset (Sum.inr (d,j)) =
      {Sum.inl a,Sum.inl b} := by
    ext x
    rw [mem_neighborFinset]
    cases x <;> simp [graph,d,Sym2.mem_iff]
  change ((graph (I:=I) C).neighborFinset (Sum.inr (d,j))).card = 2
  rw [hn]
  simp [hab.ne]

/-- Doubling each edge and subdividing both copies yields an actual simple
graph with even degree at every vertex, with no connectedness assumption. -/
theorem doubled_even_degrees (x : Vertex (I:=Fin 2) C) :
    Even ((graph (I:=Fin 2) C).degree x) := by
  classical
  cases x with
  | inl a =>
    rw [core_degree]
    simp only [Fintype.card_fin]
    exact (by decide : Even (2:ℕ)).mul_left _
  | inr z =>
    rcases z with ⟨⟨d,hd⟩,j⟩
    induction d using Sym2.inductionOn with
    | _ a b =>
      rw [branch_degree C a b ((mem_edgeSet C).mp hd) j]
      decide
/-- A subdivision branch cannot belong to a nontrivial island of
edge-connectivity at least three: its actual degree is only two. -/
theorem branch_not_highly_connected (a b : V) (hab : C.Adj a b) (j : I)
    {k : ℕ} (hk : 3≤k) (x : Vertex (I:=I) C)
    (hne : Sum.inr (⟨s(a,b),(mem_edgeSet C).mpr hab⟩,j)≠x) :
    ¬(graph (I:=I) C).IsEdgeReachable k
      (Sum.inr (⟨s(a,b),(mem_edgeSet C).mpr hab⟩,j)) x := by
  intro h
  have hle := h.le_degree hne
  rw [branch_degree C a b hab j] at hle
  omega

end LightEFTSpanners.ParallelSubdivision
