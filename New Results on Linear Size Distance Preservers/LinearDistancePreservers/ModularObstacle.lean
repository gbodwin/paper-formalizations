import LinearDistancePreservers.ModularPerfect
import LinearDistancePreservers.ObstacleCounting

/-! Concrete instantiation of the obstacle-product graph from Section 4.2.
The inner graph is the repaired modular construction. Each middle vertex
has one port pair for every inner path; the code is an explicit finite
enumeration, and all edge-disjointness inputs to the graph counts are proved.
This module does not claim uniqueness for the weighted obstacle product. -/
namespace LinearDistancePreservers.ModularObstacle
open Finset
attribute [local instance] Classical.propDecidable
variable {n k x σ : ℕ} [NeZero n] [NeZero σ]

noncomputable def portCode (σ : ℕ) (p : ZMod n × Fin x) : ZMod σ :=
  ((Fintype.equivFin (ZMod n × Fin x) p).val : ZMod σ)

theorem portCode_injective (hsize : n*x ≤ σ) :
    Function.Injective (portCode (n := n) (x := x) σ) := by
  intro p q h
  apply (Fintype.equivFin (ZMod n × Fin x)).injective
  apply Fin.ext
  have hp : (Fintype.equivFin (ZMod n × Fin x) p).val < σ := by
    have := (Fintype.equivFin (ZMod n × Fin x) p).isLt
    simp only [Fintype.card_prod, ZMod.card, Fintype.card_fin] at this
    omega
  have hq : (Fintype.equivFin (ZMod n × Fin x) q).val < σ := by
    have := (Fintype.equivFin (ZMod n × Fin x) q).isLt
    simp only [Fintype.card_prod, ZMod.card, Fintype.card_fin] at this
    omega
  simpa only [portCode, ZMod.val_natCast_of_lt hp, ZMod.val_natCast_of_lt hq]
    using congrArg ZMod.val h

noncomputable def data (hx : x ≤ n) (hsize : n*x ≤ σ) :
    ObstacleProduct.Data (ZMod σ) (ZMod σ) (ZMod σ)
      (ModularGraph.Vertex n k) (ZMod n × Fin x) k where
  left b p := b - portCode σ p
  right b p := b + portCode σ p
  inner p := ModularGraph.point p.1 p.2
  layer u := u.1.val
  inner_layer _ _ := rfl
  left_injective b := by
    intro p q h
    exact portCode_injective hsize (sub_right_inj.mp h)
  right_injective b := by
    intro p q h
    exact portCode_injective hsize (add_left_cancel h)
  inner_arc_injective := ModularGraph.arc_injective hx

theorem vertex_count :
    Fintype.card (ObstacleProduct.Vertex (ZMod σ) (ZMod σ) (ZMod σ)
      (ModularGraph.Vertex n k)) = 2*σ + σ*(k+1)*n := by
  simp [ObstacleProduct.Vertex, ModularGraph.Vertex, ZMod.card]
  ring

theorem edge_count (hx : x ≤ n) (hsize : n*x ≤ σ) :
    (ObstacleProduct.graph (data (k := k) hx hsize)).edgeFinset.card = σ*n*x*(k+2) := by
  rw [ObstacleProduct.edge_count]
  simp [ZMod.card]
  ring

end LinearDistancePreservers.ModularObstacle
