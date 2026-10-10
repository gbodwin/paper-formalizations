import GreedyShortcuts.PathFourHeight
import GreedyShortcuts.PackedChainOutput

/-! The same constructed finite chain cover and actual greedy algorithm now
use proved iterated-logarithmic four-hop preprocessing. Cubic greedy progress
and efficient cover/runtime construction remain separate. -/
namespace GreedyShortcuts.UniformChainPacking
open Finset DirectedPaths ChainUnion ChainCover
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def fourHopPackedOutput (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G)
    (r : ℕ) (hr : 3 ≤ r) : Finset (V × V) :=
  (context G hG r (6*PathFour.height r+1) (PathFour.ambientWitness r r (Nat.le_refl _))).shortcuts r (by omega)

/-- Actual legal output, explicit size and ordinary-hop guarantees, with the
chain cover and preprocessing witnesses both constructed internally. -/
theorem fourHopPackedOutput_spec (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G)
    (r : ℕ) (hr : 3 ≤ r) (hn : Fintype.card V ≤ r^3) :
    fourHopPackedOutput G hG r hr ⊆ candidates G ∧
    (fourHopPackedOutput G hG r hr).card ≤ (6*PathFour.height r+1)*Fintype.card V+50*Fintype.card V*r+2 ∧
    ∀ s t,Reachable G s t → ∃ q : DWalk s t,
      Allowed (augment G (fourHopPackedOutput G hG r hr)) q ∧ q.length ≤ 7*r+2 := by
  classical
  let T := context G hG r (6*PathFour.height r+1) (PathFour.ambientWitness r r (Nat.le_refl _))
  have hI : Fintype.card {c // c∈packing G r} ≤ r^2 := by
    have hpack := packing_card_mul G r
    have hm : (packing G r).card*r ≤ r^2*r := by nlinarith
    have hc := Nat.le_of_mul_le_mul_right hm (by omega : 0 < r)
    simpa only [Fintype.card_coe] using hc
  have hnum : 25*(Fintype.card V*Fintype.card {c // c∈packing G r}) ≤
      (25*Fintype.card V*r)*r := by
    nlinarith [Nat.mul_le_mul_left (25*Fintype.card V) hI]
  have hdiv : 25*(Fintype.card V*Fintype.card {c // c∈packing G r})/r ≤
      25*Fintype.card V*r := by
    simpa only [Nat.mul_div_cancel _ (by omega : 0 < r)] using
      Nat.div_le_div_right (c:=r) hnum
  refine ⟨T.shortcuts_legal r (by omega),?_,?_⟩
  · have hc := T.shortcuts_card_quadratic_sharp r hr
    change (fourHopPackedOutput G hG r hr).card ≤ (6*PathFour.height r+1)*Fintype.card V+
      2*(25*(Fintype.card V*Fintype.card {c // c∈packing G r})/r+1) at hc
    nlinarith
  · intro s t hst
    obtain ⟨q,hq,hlen⟩ := T.shortcuts_hop_bound
      (context_cover G hG r (6*PathFour.height r+1) (by omega)
        (PathFour.ambientWitness r r (Nat.le_refl _))) r (by omega) hst
    exact ⟨q,hq,by omega⟩



noncomputable def fourHopDefaultOutput (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G) :
    Finset (V × V) :=
  fourHopPackedOutput G hG (radius (Fintype.card V)) (radius_spec _).1

theorem fourHopDefaultOutput_spec (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G) :
    fourHopDefaultOutput G hG ⊆ candidates G ∧
    (fourHopDefaultOutput G hG).card ≤
      (6*PathFour.height (radius (Fintype.card V))+1)*Fintype.card V+
        50*Fintype.card V*radius (Fintype.card V)+2 ∧
    ∀ s t,Reachable G s t → ∃ q : DWalk s t,
      Allowed (augment G (fourHopDefaultOutput G hG)) q ∧
        q.length ≤ 7*radius (Fintype.card V)+2 :=
  fourHopPackedOutput_spec G hG _ (radius_spec _).1 (radius_spec _).2

end GreedyShortcuts.UniformChainPacking
