import GreedyShortcuts.ChainQuadraticSize
import GreedyShortcuts.ChainHopCorrectness

/-! The same full shortcut output, including preprocessing, with the proved
quadratic-derived size and ordinary-hop bounds. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainCover
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem shortcuts_card_quadratic (D : ℕ) (hD : 3 ≤ D) :
    (T.shortcuts D (by omega)).card ≤ T.K*Fintype.card V +
      (Nat.log 2 (Fintype.card V*Fintype.card I^2)+1)*
      (25*(Fintype.card V*Fintype.card I)/D+1) := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (ChainNormalization.union_card_le T.chains T.disjoint T.witnesses)
    (T.output_card_quadratic D hD))

/-- The size theorem and ordinary-hop theorem refer to one literal output.
The chain-cover and preprocessing inputs remain explicit. -/
theorem quadratic_shortcuts_spec {U : ℕ} (hcover : IsCover T U)
    (D : ℕ) (hD : 3 ≤ D) :
    T.shortcuts D (by omega) ⊆ candidates T.G ∧
    (T.shortcuts D (by omega)).card ≤ T.K*Fintype.card V +
      (Nat.log 2 (Fintype.card V*Fintype.card I^2)+1)*
      (25*(Fintype.card V*Fintype.card I)/D+1) ∧
    ∀ s t,Reachable T.G s t → ∃ q : DWalk s t,
      Allowed (augment T.G (T.shortcuts D (by omega))) q ∧ q.length ≤ 2*U+5*D+4 := by
  exact ⟨T.shortcuts_legal D (by omega),T.shortcuts_card_quadratic D hD,
    fun _ _ hr => T.shortcuts_hop_bound hcover D (by omega) hr⟩

/-- Integer-scale presentation: I<=2*r^2, target r, and at most r uncovered
vertices give at most 7*r+4 ordinary hops and an explicit n*r logarithmic
cardinality term. This is weaker than the open linear greedy-stage bound. -/
theorem quadratic_scaled_output (r : ℕ) (hr : 3 ≤ r)
    (hcover : IsCover T r) (hI : Fintype.card I ≤ 2*r^2) :
    (T.shortcuts r (by omega)).card ≤ T.K*Fintype.card V +
      (Nat.log 2 (Fintype.card V*Fintype.card I^2)+1)*
      (50*Fintype.card V*r+1) ∧
    ∀ s t,Reachable T.G s t → ∃ q : DWalk s t,
      Allowed (augment T.G (T.shortcuts r (by omega))) q ∧ q.length ≤ 7*r+4 := by
  have hnum : 25*(Fintype.card V*Fintype.card I) ≤
      (50*Fintype.card V*r)*r := by
    nlinarith [Nat.mul_le_mul_left (25*Fintype.card V) hI]
  have hdiv : 25*(Fintype.card V*Fintype.card I)/r ≤ 50*Fintype.card V*r := by
    simpa only [Nat.mul_div_cancel _ (by omega : 0<r)] using Nat.div_le_div_right (c:=r) hnum
  constructor
  · exact (T.shortcuts_card_quadratic r hr).trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hdiv 1)) _)
  · intro s t hst
    obtain ⟨q,hq,hlen⟩ := T.shortcuts_hop_bound hcover r (by omega) hst
    exact ⟨q,hq,by omega⟩

end GreedyShortcuts.ChainDistance.Context
