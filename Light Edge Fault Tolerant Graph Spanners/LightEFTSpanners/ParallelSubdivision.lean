import LightEFTSpanners.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic

/-! An actual parallel edge-subdivision model for the Section4.1 construction.
Each original edge gets a distinct degree-two vertex for every copy index. -/
namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
variable {V I : Type*} (C : SimpleGraph V)

abbrev Vertex := V ⊕ (C.edgeSet × I)

def graph : SimpleGraph (Vertex (I:=I) C) where
  Adj a b := match a,b with
    | Sum.inl u,Sum.inr z => u∈(z.1:Sym2 V)
    | Sum.inr z,Sum.inl u => u∈(z.1:Sym2 V)
    | _,_ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

def colorGraph (j : I) : SimpleGraph (Vertex (I:=I) C) where
  Adj a b := match a,b with
    | Sum.inl u,Sum.inr z => u∈(z.1:Sym2 V) ∧ z.2=j
    | Sum.inr z,Sum.inl u => u∈(z.1:Sym2 V) ∧ z.2=j
    | _,_ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

theorem colorGraph_le (j : I) : colorGraph C j ≤ graph (I:=I) C := by
  intro a b h
  cases a <;> cases b <;> simp_all [colorGraph,graph]

theorem colorGraph_disjoint {i j : I} (hij : i≠j) :
    Disjoint (colorGraph C i) (colorGraph C j) := by
  apply SimpleGraph.disjoint_left.mpr
  intro a b hai haj
  cases a <;> cases b <;> simp_all [colorGraph]

theorem color_edge_has_copy {j : I} {e : Sym2 (Vertex (I:=I) C)}
    (he : e∈(colorGraph C j).edgeSet) :
    ∃ (a : V) (d : C.edgeSet), e=s(Sum.inl a,Sum.inr (d,j)) := by
  rcases e with ⟨a,b⟩
  have hab := (mem_edgeSet _).mp he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact False.elim hab
    | inr z =>
      obtain ⟨hz,hj⟩ := hab
      exact ⟨a,z.1,congrArg (fun z => s(Sum.inl a,Sum.inr z)) (Prod.ext rfl hj)⟩
  | inr z =>
    cases b with
    | inl b =>
      obtain ⟨hz,hj⟩ := hab
      have hzj : z=(z.1,j) := Prod.ext rfl hj
      refine ⟨b,z.1,?_⟩
      calc
        _ = s(Sum.inl b,Sum.inr z) := Sym2.eq_swap
        _ = s(Sum.inl b,Sum.inr (z.1,j)) :=
          congrArg (fun zz : C.edgeSet × I =>
            (s(Sum.inl b,Sum.inr zz) : Sym2 (Vertex (I:=I) C))) hzj
    | inr z' => exact False.elim hab

/-- Any surviving base edge lifts to an actual two-edge path of a fixed color. -/
theorem base_edge_reachable {u v : V} (huv : C.Adj u v) (j : I)
    (F : Finset (Sym2 (Vertex (I:=I) C)))
    (hclean : ∀ a : V, a∈s(u,v) → s(Sum.inl a,Sum.inr (⟨s(u,v),(mem_edgeSet C).mpr huv⟩,j))∉F) :
    (afterFaults (graph (I:=I) C) F).Reachable (Sum.inl u) (Sum.inl v) := by
  let d : C.edgeSet := ⟨s(u,v),(mem_edgeSet C).mpr huv⟩
  have hu : (afterFaults (graph (I:=I) C) F).Adj (Sum.inl u) (Sum.inr (d,j)) :=
    deleteEdges_adj.mpr ⟨by simp [graph,d],hclean u (by simp)⟩
  have hv : (afterFaults (graph (I:=I) C) F).Adj (Sum.inl v) (Sum.inr (d,j)) :=
    deleteEdges_adj.mpr ⟨by simp [graph,d],hclean v (by simp)⟩
  exact hu.reachable.trans hv.reachable.symm
end LightEFTSpanners.ParallelSubdivision
