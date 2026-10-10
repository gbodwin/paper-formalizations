import LengthExpander.Demands
import LengthExpander.ParallelGreedy
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! A directed integral demand is represented by an undirected matching on
separate outgoing and incoming copies. This repairs Appendix A's use of one
copy set, which cannot in general encode asymmetric ordered demands. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

abbrev DemandCopies (A : NodeWeight V) := (u : V) × Fin (A u)
abbrev DemandUnits (D : Demand V) := (u : V) × (v : V) × Fin (D u v)
abbrev DirectedCopies (A : NodeWeight V) := DemandCopies A ⊕ DemandCopies A

def copyVertex {A : NodeWeight V} : DirectedCopies A → V
  | Sum.inl u => u.1
  | Sum.inr u => u.1

@[simp] theorem card_demandUnits (D : Demand V) :
    Fintype.card (DemandUnits D) = demandSize D := by
  simp [DemandUnits,demandSize,Fintype.card_sigma]

@[simp] theorem card_directedCopies (A : NodeWeight V) :
    Fintype.card (DirectedCopies A) = 2 * weightSize A := by
  simp [DirectedCopies,DemandCopies,weightSize,Fintype.card_sigma,two_mul]

/-- The source and target allocations are separate, so only the row and
column inequalities in `Respects` are needed. -/
structure DemandAllocation (D : Demand V) (A : NodeWeight V) where
  source : DemandUnits D ↪ DemandCopies A
  target : DemandUnits D ↪ DemandCopies A
  source_vertex : ∀ t, (source t).1 = t.1
  target_vertex : ∀ t, (target t).1 = t.2.1

noncomputable def demandAllocation {D : Demand V} {A : NodeWeight V}
    (hD : Respects D A) : DemandAllocation D A := by
  classical
  let f (u : V) : ((v : V) × Fin (D u v)) ↪ Fin (A u) :=
    (Function.Embedding.nonempty_of_card_le (by simpa using hD.1 u)).some
  let g (v : V) : ((u : V) × Fin (D u v)) ↪ Fin (A v) :=
    (Function.Embedding.nonempty_of_card_le (by simpa using hD.2 v)).some
  let swap : DemandUnits D ≃ ((v : V) × (u : V) × Fin (D u v)) :=
    ⟨fun t => ⟨t.2.1,t.1,t.2.2⟩,fun t => ⟨t.2.1,t.1,t.2.2⟩,
      fun _ => rfl,fun _ => rfl⟩
  exact ⟨Function.Embedding.sigmaMap (.refl V) f,
    swap.toEmbedding.trans (Function.Embedding.sigmaMap (.refl V) g),
    fun _ => rfl,fun _ => rfl⟩

namespace DemandAllocation
variable {D : Demand V} {A : NodeWeight V} (a : DemandAllocation D A)

def left (t : DemandUnits D) : DirectedCopies A := Sum.inl (a.source t)
def right (t : DemandUnits D) : DirectedCopies A := Sum.inr (a.target t)
def unitEdge (t : DemandUnits D) : Sym2 (DirectedCopies A) := s(a.left t,a.right t)

theorem left_injective : Function.Injective a.left := by
  intro t u h
  exact a.source.injective (Sum.inl.inj h)

theorem right_injective : Function.Injective a.right := by
  intro t u h
  exact a.target.injective (Sum.inr.inj h)

theorem left_ne_right (t u : DemandUnits D) : a.left t ≠ a.right u := by
  simp [left,right]

theorem unitEdge_injective : Function.Injective a.unitEdge := by
  intro t u h
  rcases Sym2.eq_iff.mp h with h | h
  · exact a.left_injective h.1
  · exact (a.left_ne_right t u h.1).elim

/-- Two encoded demand units never share a copy. -/
theorem shared_endpoint {t u : DemandUnits D} {z : DirectedCopies A}
    (ht : z ∈ a.unitEdge t) (hu : z ∈ a.unitEdge u) : t = u := by
  rcases Sym2.mem_iff.mp ht with ht | ht <;>
    rcases Sym2.mem_iff.mp hu with hu | hu
  · exact a.left_injective (ht.symm.trans hu)
  · exact (a.left_ne_right t u (ht.symm.trans hu)).elim
  · exact (a.left_ne_right u t (hu.symm.trans ht)).elim
  · exact a.right_injective (ht.symm.trans hu)

def graph : SimpleGraph (DirectedCopies A) where
  Adj x y := ∃ t, (x = a.left t ∧ y = a.right t) ∨
    (x = a.right t ∧ y = a.left t)
  symm.symm _ _ h := by
    obtain ⟨t,h | h⟩ := h
    · exact ⟨t,Or.inr ⟨h.2,h.1⟩⟩
    · exact ⟨t,Or.inl ⟨h.2,h.1⟩⟩
  loopless.irrefl x h := by
    obtain ⟨t,h | h⟩ := h
    · exact a.left_ne_right t t (h.1.symm.trans h.2)
    · exact a.left_ne_right t t (h.2.symm.trans h.1)

theorem graph_adj_iff (x y : DirectedCopies A) :
    a.graph.Adj x y ↔ ∃ t, s(x,y) = a.unitEdge t := by
  simp only [graph,unitEdge,Sym2.eq_iff]

/-- The graph is an actual matching, without any label-dependent premise. -/
theorem graph_matching (x y z : DirectedCopies A)
    (hx : a.graph.Adj x z) (hy : a.graph.Adj y z) : x = y := by
  obtain ⟨t,ht⟩ := (a.graph_adj_iff x z).mp hx
  obtain ⟨u,hu⟩ := (a.graph_adj_iff y z).mp hy
  have htu : t = u := a.shared_endpoint
    (ht ▸ Sym2.mem_mk_right x z) (hu ▸ Sym2.mem_mk_right y z)
  subst u
  exact Sym2.congr_left.mp (ht.trans hu.symm)

noncomputable def edgeEquiv : DemandUnits D ≃ a.graph.edgeSet := by
  classical
  apply Equiv.ofBijective (fun t => ⟨a.unitEdge t,by
    exact ⟨t,Or.inl ⟨rfl,rfl⟩⟩⟩)
  constructor
  · intro t u h
    exact a.unitEdge_injective (congrArg Subtype.val h)
  · intro e
    obtain ⟨⟨x,y⟩,he⟩ := e
    obtain ⟨t,ht⟩ := (a.graph_adj_iff x y).mp he
    exact ⟨t,Subtype.ext ht.symm⟩

/-- There is exactly one graph edge for each directed integral demand unit. -/
theorem graph_edge_card : Fintype.card a.graph.edgeSet = demandSize D := by
  rw [← Fintype.card_congr a.edgeEquiv,card_demandUnits]

theorem graph_edge_projection (t : DemandUnits D) :
    copyVertex (a.left t) = t.1 ∧ copyVertex (a.right t) = t.2.1 :=
  ⟨a.source_vertex t,a.target_vertex t⟩


/-- Any symmetric property of the supported ordered pair transfers to the
endpoints of its copy edge. -/
theorem graph_property (P : V → V → Prop) (hP : Symmetric P)
    (hD : ∀ u v, 0 < D u v → P u v) {x y : DirectedCopies A}
    (hxy : a.graph.Adj x y) : P (copyVertex x) (copyVertex y) := by
  obtain ⟨t,h⟩ := hxy
  have ht : P t.1 t.2.1 := hD _ _ (Nat.zero_lt_of_lt t.2.2.isLt)
  have hv := a.graph_edge_projection t
  rcases h with h | h
  · rw [h.1,h.2,hv.1,hv.2]
    exact ht
  · rw [h.1,h.2,hv.1,hv.2]
    exact hP ht

end DemandAllocation
end LengthExpander
