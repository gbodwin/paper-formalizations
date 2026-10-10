import LengthExpander.DirectedDemandMatching
import LengthExpander.MatchingMetricBridge

/-! A finite sequence of support-disjoint directed demands yields a simple
union of matchings with exact edge accounting and reversed stage labels. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {k : ℕ} {D : Fin k → Demand V} {A : NodeWeight V}

abbrev FamilyUnits (D : Fin k → Demand V) := (i : Fin k) × DemandUnits (D i)

def SupportDisjoint (D : Fin k → Demand V) : Prop :=
  ∀ i j, i ≠ j → ∀ u v, D i u v = 0 ∨ D j u v = 0

def familyEdge (a : ∀ i, DemandAllocation (D i) A) (t : FamilyUnits D) :
    Sym2 (DirectedCopies A) := (a t.1).unitEdge t.2

theorem familyEdge_injective (a : ∀ i, DemandAllocation (D i) A)
    (hd : SupportDisjoint D) : Function.Injective (familyEdge a) := by
  intro t u he
  have hi : t.1 = u.1 := by
    by_contra hne
    have hep : (a t.1).left t.2 = (a u.1).left u.2 ∧
        (a t.1).right t.2 = (a u.1).right u.2 := by
      rcases Sym2.eq_iff.mp he with hh | hh
      · exact hh
      · have hf := hh.1
        cases hf
    have hs : t.2.1 = u.2.1 := by
      have := congrArg copyVertex hep.1
      simpa [DemandAllocation.left,copyVertex,(a t.1).source_vertex,(a u.1).source_vertex] using this
    have ht : t.2.2.1 = u.2.2.1 := by
      have := congrArg copyVertex hep.2
      simpa [DemandAllocation.right,copyVertex,(a t.1).target_vertex,(a u.1).target_vertex] using this
    rcases hd t.1 u.1 hne t.2.1 t.2.2.1 with hz | hz
    · have := t.2.2.2.isLt
      omega
    · have hz' : D u.1 u.2.1 u.2.2.1 = 0 := by simpa only [hs,ht] using hz
      have := u.2.2.2.isLt
      omega
  rcases t with ⟨i,t⟩
  rcases u with ⟨j,u⟩
  dsimp at hi
  subst j
  have htu : t = u := (a i).unitEdge_injective he
  subst u
  rfl

def familyGraph (a : ∀ i, DemandAllocation (D i) A) : SimpleGraph (DirectedCopies A) where
  Adj x y := ∃ i, (a i).graph.Adj x y
  symm.symm _ _ h := by obtain ⟨i,hi⟩ := h; exact ⟨i,hi.symm⟩
  loopless.irrefl _ h := by obtain ⟨i,hi⟩ := h; exact hi.ne rfl

theorem familyGraph_adj_iff (a : ∀ i, DemandAllocation (D i) A) (x y : DirectedCopies A) :
    (familyGraph a).Adj x y ↔ ∃ t, s(x,y) = familyEdge a t := by
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨t,ht⟩ := ((a i).graph_adj_iff x y).mp hi
    exact ⟨⟨i,t⟩,ht⟩
  · rintro ⟨⟨i,t⟩,ht⟩
    exact ⟨i,((a i).graph_adj_iff x y).mpr ⟨t,ht⟩⟩

noncomputable def familyEdgeEquiv (a : ∀ i, DemandAllocation (D i) A)
    (hd : SupportDisjoint D) : FamilyUnits D ≃ (familyGraph a).edgeSet := by
  classical
  apply Equiv.ofBijective (fun t => ⟨familyEdge a t,⟨t.1,t.2,Or.inl ⟨rfl,rfl⟩⟩⟩)
  constructor
  · intro t u h
    exact familyEdge_injective a hd (congrArg Subtype.val h)
  · intro e
    obtain ⟨⟨x,y⟩,he⟩ := e
    obtain ⟨t,ht⟩ := (familyGraph_adj_iff a x y).mp he
    exact ⟨t,Subtype.ext ht.symm⟩

theorem familyGraph_edge_card (a : ∀ i, DemandAllocation (D i) A)
    (hd : SupportDisjoint D) :
    Fintype.card (familyGraph a).edgeSet = ∑ i, demandSize (D i) := by
  rw [← Fintype.card_congr (familyEdgeEquiv a hd)]
  simp [FamilyUnits,Fintype.card_sigma,demandSize]

/-- Reverse chronological order. The default value on nonedges is irrelevant. -/
noncomputable def reverseIndex (a : ∀ i, DemandAllocation (D i) A)
    (e : Sym2 (DirectedCopies A)) : ℕ :=
  if h : ∃ t, familyEdge a t = e then k - ((Classical.choose h).1.val + 1) else 0

theorem reverseIndex_edge (a : ∀ i, DemandAllocation (D i) A)
    (hd : SupportDisjoint D) (t : FamilyUnits D) :
    reverseIndex a (familyEdge a t) = k - (t.1.val + 1) := by
  have h : ∃ u, familyEdge a u = familyEdge a t := ⟨t,rfl⟩
  rw [reverseIndex,dif_pos h]
  have he := familyEdge_injective a hd (Classical.choose_spec h)
  rw [he]

theorem familyGraph_matchingLabels (a : ∀ i, DemandAllocation (D i) A)
    (hd : SupportDisjoint D) : MatchingLabels (familyGraph a) (reverseIndex a) := by
  intro x y z hx hy he
  obtain ⟨⟨i,t⟩,ht⟩ := (familyGraph_adj_iff a x z).mp hx
  obtain ⟨⟨j,u⟩,hu⟩ := (familyGraph_adj_iff a y z).mp hy
  rw [ht,hu,reverseIndex_edge a hd,reverseIndex_edge a hd] at he
  have hij : i = j := by apply Fin.ext; have := i.isLt; have := j.isLt; dsimp at he; omega
  subst j
  exact (a i).graph_matching x y z
    (((a i).graph_adj_iff x z).mpr ⟨t,ht⟩)
    (((a i).graph_adj_iff y z).mpr ⟨u,hu⟩)

end LengthExpander
