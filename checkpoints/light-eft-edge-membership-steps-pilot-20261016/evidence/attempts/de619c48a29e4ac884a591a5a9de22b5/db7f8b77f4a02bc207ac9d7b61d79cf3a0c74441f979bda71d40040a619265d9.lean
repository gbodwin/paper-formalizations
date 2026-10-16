import LightEFTSpanners.NativeColorCrossings
import LightEFTSpanners.NativeCrossingNonbridge
import Mathlib.Algebra.BigOperators.Fin

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The source proof's terminal-quotient counting step, using actual colored
native trees. The partition condition and exact original-ID color sum force
the last quotient to have at least one fewer edge than the number of blocks. -/
theorem last_color_quotient_dense (G : Graph V E) {k m : ℕ}
    (f : V → Fin m) (hsurj : Function.Surjective (fun a : G.vertexSet => f a))
    (color : E → Fin (k+1)) (hp : TreePartitionCriterion G (k+1))
    (hc : ∀ c : Fin k,∀ a b : G.vertexSet,f a=f b →
      (blockGraph (G.restrict {e | color e=c.castSucc}).toSimpleGraph
        (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    (ht : ∀ c : Fin k,
      (∀ e∈(G.restrict {e | color e=c.castSucc}).edgeSet,
        (G.restrict {e | color e=c.castSucc}).IsBridge e) ∧
      (G.restrict {e | color e=c.castSucc}).toSimpleGraph.Connected) :
    m≤Nat.card (crossingQuotient (G.restrict {e | color e=Fin.last k}) f).edgeSet+1 := by
  classical
  have himage : f '' G.vertexSet=Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro i
    obtain ⟨a,ha⟩ := hsurj i
    exact ⟨a.val,a.property,ha⟩
  have htree : ∀ c : Fin k,
      Nat.card (crossingQuotient (G.restrict {e | color e=c.castSucc}) f).edgeSet=m-1 := by
    intro c
    have hh := tree_crossingQuotient_card (G.restrict {e | color e=c.castSucc}) f
      (hc c) (ht c).1 (ht c).2
    change _+1=Nat.card (f '' G.vertexSet) at hh
    rw [himage] at hh
    simp only [Nat.card_univ,Nat.card_fin] at hh
    omega
  have hsum := color_crossing_card_sum G f color
  rw [Fin.sum_univ_castSucc] at hsum
  have hfirst : (∑ c : Fin k,
      Nat.card (crossingQuotient (G.restrict {e | color e=c.castSucc}) f).edgeSet)=k*(m-1) := by
    simp_rw [htree]
    simp
  rw [hfirst] at hsum
  have hbudget := hp m (fun a : G.vertexSet => f a) hsurj
  rw [actualPartitionCrossings_eq] at hbudget
  have hlast : m-1≤Nat.card
      (crossingQuotient (G.restrict {e | color e=Fin.last k}) f).edgeSet := by
    rw [← hsum] at hbudget
    nlinarith
  omega
/-- The complete terminal-partition obstruction before the exchange step:
actual first colors are trees, every color connects each fiber, and the last
color is disconnected. The partition condition forces a crossing edge of the
last color with an actual alternate path after deleting that same identity. -/
theorem terminal_last_color_crossing_nonbridge (G : Graph V E) {k m : ℕ}
    (f : V → Fin m) (hsurj : Function.Surjective (fun a : G.vertexSet => f a))
    (color : E → Fin (k+1)) (hp : TreePartitionCriterion G (k+1))
    (hc : ∀ c : Fin (k+1),∀ a b : G.vertexSet,f a=f b →
      (blockGraph (G.restrict {e | color e=c}).toSimpleGraph
        (Setoid.ker (fun a : G.vertexSet => f a))).Reachable a b)
    (ht : ∀ c : Fin k,
      (∀ e∈(G.restrict {e | color e=c.castSucc}).edgeSet,
        (G.restrict {e | color e=c.castSucc}).IsBridge e) ∧
      (G.restrict {e | color e=c.castSucc}).toSimpleGraph.Connected)
    {a b : G.vertexSet}
    (hnot : ¬(G.restrict {e | color e=Fin.last k}).toSimpleGraph.Reachable a b) :
    ∃ e u v,∃ he : G.IsLink e u v,color e=Fin.last k ∧ f u≠f v ∧
      ¬(G.restrict {e | color e=Fin.last k}).IsBridge e ∧
      ((G.restrict {e | color e=Fin.last k}).deleteEdges {e}).toSimpleGraph.Reachable
        ⟨u,he.left_mem⟩ ⟨v,he.right_mem⟩ := by
  have hd := last_color_quotient_dense G f hsurj color hp (fun c => hc c.castSucc) ht
  have himage : f '' G.vertexSet=Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro i
    obtain ⟨x,hx⟩ := hsurj i
    exact ⟨x.val,x.property,hx⟩
  have hcard : Nat.card (f '' (G.restrict {e | color e=Fin.last k}).vertexSet)=m := by
    change Nat.card (f '' G.vertexSet)=m
    rw [himage]
    simp
  obtain ⟨e,u,v,he,hne,hnb,hr⟩ := exists_crossing_nonbridge_of_dense_quotient
    (G.restrict {e | color e=Fin.last k}) f (hc (Fin.last k)) hnot (by simpa only [hcard] using hd)
  exact ⟨e,u,v,he.2,he.1,hne,hnb,hr⟩
end LightEFTSpanners.MultigraphCuts
