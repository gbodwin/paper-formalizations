import LengthExpander.DemandMatchingFamily

/-! The geometric hypotheses are exactly those of demands witnessed before
and separated after consecutive length-increase cuts. They imply disjoint
support and certify the actual constructed copy graph as parallel greedy. -/
namespace LengthExpander
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {k s : ℕ} {D : Fin k → Demand V} {A : NodeWeight V}

theorem far_symm {w : EdgeLength V} {h : ℝ} {u v : V}
    (hf : Far G w h u v) : Far G w h v u := by
  intro p
  simpa using hf p.reverse

structure SequentialDemandGeometry (G : SimpleGraph V) (w : ℕ → EdgeLength V)
    (h : ℝ) (s : ℕ) (D : Fin k → Demand V) : Prop where
  monotone : ∀ i j, i ≤ j → ∀ e, w i e ≤ w j e
  near : ∀ i u v, 0 < D i u v → Near G (w i.val) h u v
  far : ∀ i u v, 0 < D i u v → Far G (w (i.val+1)) (h*s) u v

namespace SequentialDemandGeometry
variable {w : ℕ → EdgeLength V} {h : ℝ}
    (geo : SequentialDemandGeometry G w h s D)
include geo

theorem supportDisjoint (hh : 0 ≤ h) (hs : 1 ≤ s) : SupportDisjoint D := by
  intro i j hne u v
  by_contra hz
  push_neg at hz
  have hi : 0 < D i u v := Nat.pos_of_ne_zero hz.1
  have hj : 0 < D j u v := Nat.pos_of_ne_zero hz.2
  have hbound : h ≤ h*s := by
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hn := near_length_mono (geo.monotone (i.val+1) j.val (by exact hij)) (geo.near j u v hj)
    obtain ⟨p,hp⟩ := hn
    exact (not_lt_of_ge (hp.trans hbound)) (geo.far i u v hi p)
  · have hn := near_length_mono (geo.monotone (j.val+1) i.val (by exact hji)) (geo.near i u v hi)
    obtain ⟨p,hp⟩ := hn
    exact (not_lt_of_ge (hp.trans hbound)) (geo.far j u v hj p)

/-- Lemma A.2, repaired to separate outgoing and incoming copies. The graph
has exactly 2|A| vertices and sum_i |D_i| edges; the matching construction,
edge disjointness, and earlier-walk exclusion are all derived. -/
theorem parallelGreedy (a : ∀ i, DemandAllocation (D i) A)
    (hh : 0 ≤ h) (hs : 1 ≤ s) :
    IsParallelGreedy (familyGraph a) (reverseIndex a) s := by
  have hd := geo.supportDisjoint hh hs
  refine ⟨familyGraph_matchingLabels a hd,?_⟩
  intro x y hxy p hlen hbefore
  obtain ⟨⟨i,t⟩,ht⟩ := (familyGraph_adj_iff a x y).mp hxy
  have hiadj : (a i).graph.Adj x y := ((a i).graph_adj_iff x y).mpr ⟨t,ht⟩
  have hfar : Far G (w (i.val+1)) (h*s) (copyVertex x) (copyVertex y) :=
    (a i).graph_property _ (fun _ _ => far_symm) (geo.far i) hiadj
  have hn := near_of_copy_walk copyVertex (w (i.val+1)) h p (by
    intro u v huv he
    obtain ⟨⟨j,q⟩,hq⟩ := (familyGraph_adj_iff a u v).mp huv
    have hr := hbefore s(u,v) he
    rw [ht,hq,reverseIndex_edge a hd,reverseIndex_edge a hd] at hr
    have hij : i.val+1 ≤ j.val := by have := i.isLt; have := j.isLt; dsimp at hr; omega
    have hjadj : (a j).graph.Adj u v := ((a j).graph_adj_iff u v).mpr ⟨q,hq⟩
    exact near_length_mono (geo.monotone _ _ hij)
      ((a j).graph_property _ (fun _ _ => near_symm) (geo.near j) hjadj))
  obtain ⟨q,hq⟩ := hn
  have hbound : (p.length : ℝ)*h ≤ h*s := by
    have hl : (p.length : ℝ) ≤ s := by exact_mod_cast hlen
    nlinarith
  exact (not_lt_of_ge (hq.trans hbound)) (hfar q)

end SequentialDemandGeometry
end LengthExpander
