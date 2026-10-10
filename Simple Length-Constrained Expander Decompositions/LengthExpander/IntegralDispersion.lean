import LengthExpander.OrientationDispersion
import LengthExpander.PushforwardDemand
import LengthExpander.ScaledIntegralExtraction
import LengthExpander.DispersedPairGeometry

/-! Construct a large integral original-vertex demand from the repaired copy
graph. Sparse orientation replaces rooted forest dispersion; all incidence,
fibre, integrality, support, and mass losses are explicit. -/
namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {A : NodeWeight V}

theorem exists_integral_dispersion {H : SimpleGraph (DirectedCopies A)}
    {index : Sym2 (DirectedCopies A) → ℕ} {s : ℕ}
    (hH : IsParallelGreedy H index s) (hs : 2 ≤ s) :
    ∃ D : Demand V, Respects D A ∧
      (∀ u v, 0 < D u v → ∃ x y : DirectedCopies A,
        copyVertex x = u ∧ copyVertex y = v ∧ CopyShortPair H x y) ∧
      Fintype.card H.edgeSet ≤ 8*(densityBudget (2*weightSize A) s+1)*demandSize D := by
  classical
  obtain ⟨L,hnd,hcover,horder⟩ := parallelGreedy_sparse_order hH hs
  let K := densityBudget (2*weightSize A) s
  have horder' : SparseOrder H K L := by
    unfold K
    exact (card_directedCopies A) ▸ horder
  let B := orientationDispersion H L
  have hB : Respects B (fun _ => K+1) := by
    constructor
    · intro x
      have hi := orientationDispersion_incidence horder' hcover x
      exact (Nat.le_add_right _ _).trans hi
    · intro x
      have hi := orientationDispersion_incidence horder' hcover x
      exact (Nat.le_add_left _ _).trans hi
  let C := pushDemand copyVertex B
  have hCP := pushDemand_respects copyVertex hB
  have hC : Respects C (fun u => (2*(K+1))*A u) := by
    constructor
    · intro u
      exact (hCP.1 u).trans_eq (by dsimp only; rw [copy_vertexFiber_card]; ring)
    · intro u
      exact (hCP.2 u).trans_eq (by dsimp only; rw [copy_vertexFiber_card]; ring)
  obtain ⟨D,hD,hsupport,hm⟩ := exists_integral_of_scaled_budgets C A (2*(K+1)) (by omega) hC
  refine ⟨D,hD,?_,?_⟩
  · intro u v huv
    obtain ⟨x,y,hx,hy,hxy⟩ := pushDemand_positive copyVertex (hsupport u v huv)
    exact ⟨x,y,hx,hy,orientationDispersion_support hxy⟩
  · have hlarge := orientationDispersion_large H L hcover
    have hsize : demandSize C = demandSize B := pushDemand_size copyVertex B
    dsimp only [B] at hsize
    rw [hsize] at hm
    dsimp only [K] at hm
    nlinarith

end LengthExpander
