import LengthExpander.SequentialDemandGeometry

/-! Every single matching edge, or two distinct edges meeting at a copy,
gives a short original pair separated by the final prefix metric. This
preserves the strict inequality required by the cut-witness definition. -/
namespace LengthExpander
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {k s : ℕ} {D : Fin k → Demand V} {A : NodeWeight V}

theorem far_length_mono {w w' : EdgeLength V}
    (hw : ∀ e, w e ≤ w' e) {h : ℝ} {u v : V}
    (hf : Far G w h u v) : Far G w' h u v := by
  intro p
  exact (hf p).trans_le (walkLength_mono hw p)

def CopyShortPair (H : SimpleGraph (DirectedCopies A)) (x y : DirectedCopies A) : Prop :=
  H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y ∧ x ≠ y

namespace SequentialDemandGeometry
variable {w : ℕ → EdgeLength V} {h : ℝ}
    (geo : SequentialDemandGeometry G w h s D)
    (a : ∀ i, DemandAllocation (D i) A)
include geo

theorem family_edge_near {x y : DirectedCopies A} (hxy : (familyGraph a).Adj x y) :
    Near G (w 0) h (copyVertex x) (copyVertex y) := by
  obtain ⟨i,hi⟩ := hxy
  exact near_length_mono (geo.monotone 0 i.val (Nat.zero_le _))
    ((a i).graph_property _ (fun _ _ => near_symm) (geo.near i) hi)

theorem short_pair_near (hh : 0 ≤ h) {x y : DirectedCopies A}
    (hxy : CopyShortPair (familyGraph a) x y) :
    Near G (w 0) (2*h) (copyVertex x) (copyVertex y) := by
  rcases hxy with he | ⟨z,hxz,hzy,_⟩
  · obtain ⟨p,hp⟩ := geo.family_edge_near a he
    exact ⟨p,by linarith⟩
  · have hn := near_triangle (geo.family_edge_near a hxz) (geo.family_edge_near a hzy)
    simpa only [two_mul] using hn

theorem short_pair_far (hh : 0 ≤ h) {x y : DirectedCopies A}
    (hxy : CopyShortPair (familyGraph a) x y) :
    Far G (w k) (h*((s:ℝ)-1)) (copyVertex x) (copyVertex y) := by
  rcases hxy with ⟨i,hi⟩ | ⟨z,⟨i,hi⟩,⟨j,hj⟩,hne⟩
  · have hf := (a i).graph_property _ (fun _ _ => far_symm) (geo.far i) hi
    have hf' := far_length_mono (geo.monotone (i.val+1) k i.isLt) hf
    intro p
    have hp := hf' p
    nlinarith
  · have hij : i ≠ j := by
      intro he
      subst j
      exact hne ((a i).graph_matching x y z hi hj.symm)
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hf := (a i).graph_property _ (fun _ _ => far_symm) (geo.far i) hi
      have hn := near_length_mono (geo.monotone (i.val+1) j.val hij)
        ((a j).graph_property _ (fun _ _ => near_symm) (geo.near j) hj)
      exact far_length_mono (geo.monotone (i.val+1) k i.isLt) (dispersed_pair_far hf hn)
    · have hf := (a j).graph_property _ (fun _ _ => far_symm) (geo.far j) hj.symm
      have hn := near_length_mono (geo.monotone (j.val+1) i.val hji)
        ((a i).graph_property _ (fun _ _ => near_symm) (geo.near i) hi.symm)
      exact far_symm (far_length_mono (geo.monotone (j.val+1) k j.isLt) (dispersed_pair_far hf hn))

end SequentialDemandGeometry
end LengthExpander
