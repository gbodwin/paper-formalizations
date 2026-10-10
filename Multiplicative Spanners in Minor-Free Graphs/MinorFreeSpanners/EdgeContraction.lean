import MinorFreeSpanners.BoundedMinor
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! A genuine single-edge contraction, with the removed endpoint absent
from the resulting vertex type. This will support minor-minimal extraction. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V) (u v : V)

/-- Contract v into u, deleting v and merging parallel adjacencies. -/
def contractEdge : SimpleGraph {x : V // x ≠ v} where
  Adj a b := a ≠ b ∧ (G.Adj a.val b.val ∨
    (a.val = u ∧ G.Adj v b.val) ∨ (b.val = u ∧ G.Adj a.val v))
  symm := ⟨by
    rintro a b ⟨hne,h | h | h⟩
    · exact ⟨hne.symm,Or.inl h.symm⟩
    · exact ⟨hne.symm,Or.inr (Or.inr ⟨h.1,h.2.symm⟩)⟩
    · exact ⟨hne.symm,Or.inr (Or.inl ⟨h.1,h.2.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The contraction is witnessed by actual singleton branches except for
one connected two-vertex branch {u,v}. -/
def contractEdgeModel (huv : G.Adj u v) : MinorModel (contractEdge G u v) G where
  branch := fun i => {x | x = i.val ∨ (i.val = u ∧ x = v)}
  nonempty := fun i => ⟨i.val,Or.inl rfl⟩
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | ⟨hi,hx⟩ <;> rcases hy with hy | ⟨hj,hy⟩
    · exact hij (Subtype.ext (hx.symm.trans hy))
    · exact i.property (hx.symm.trans hy)
    · exact j.property (hy.symm.trans hx)
    · exact hij (Subtype.ext (hi.trans hj.symm))
  connected := by
    intro i a ha b hb
    rcases ha with ha | ⟨hi,ha⟩ <;> rcases hb with hb | ⟨hj,hb⟩
    all_goals subst a; subst b
    · exact ⟨.nil,by simp⟩
    · have h : G.Adj i.val v := by simpa [hj] using huv
      refine ⟨.cons h .nil,?_⟩
      intro z hz
      simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨hj,rfl⟩
    · have h : G.Adj v i.val := by simpa [hi] using huv.symm
      refine ⟨.cons h .nil,?_⟩
      intro z hz
      simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact Or.inr ⟨hi,rfl⟩
      · exact Or.inl rfl
    · exact ⟨.nil,by simp [hi]⟩
  adjacent := by
    rintro i j ⟨_,h | ⟨hi,h⟩ | ⟨hj,h⟩⟩
    · exact ⟨i.val,Or.inl rfl,j.val,Or.inl rfl,h⟩
    · exact ⟨v,Or.inr ⟨hi,rfl⟩,j.val,Or.inl rfl,h⟩
    · exact ⟨i.val,Or.inl rfl,v,Or.inr ⟨hj,rfl⟩,h⟩

theorem contractEdgeModel_bounded [Fintype V] (huv : G.Adj u v) :
    (contractEdgeModel G u v huv).IsBounded 2 := by
  classical
  intro i
  have hs : (contractEdgeModel G u v huv).branch i ⊆ {i.val,v} := by
    intro x hx
    rcases hx with rfl | ⟨_,rfl⟩ <;> simp
  have hc : ((contractEdgeModel G u v huv).branch i).toFinset.card ≤
      ({i.val,v}:Finset V).card := by
    apply Finset.card_le_card
    intro x hx
    simpa using hs (Set.mem_toFinset.mp hx)
  simpa [i.property] using hc

/-- One vertex, and no additional isolated endpoint, is removed. -/
theorem contractEdge_vertex_card [Fintype V] [DecidableEq V] :
    Fintype.card {x : V // x ≠ v} = Fintype.card V - 1 := by
  classical
  simpa using Fintype.card_subtype_compl (fun x : V => x = v)

end MinorFreeSpanners
