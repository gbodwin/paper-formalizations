import SlackSparsification.PlusFourMedium
import SlackSparsification.PathPurchases
import Mathlib.Tactic

/-! Theorem 12: choose the largest of the short, medium and long classes.
This gives a fixed 1/12 slack fraction and simplifies overlap bookkeeping.
All three constructions are actual subgraphs, with explicit integer budgets. -/
namespace SlackSparsification
open Finset SimpleGraph
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

theorem exists_plus_four_slack_paths (G : SimpleGraph V)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (d m K : ℕ) (hd : 0 < d) :
    ∃ (H : SimpleGraph V) (Q : Finset D), H ≤ G ∧ Q ⊆ P ∧ P.card ≤ 12 * Q.card ∧
      H.edgeFinset.card ≤ 3 * Fintype.card V * d + 2 * P.card * m +
        (2 * (2 * Fintype.card V / (d * (m + 1)) + 1)) ^ 2 * K +
        Fintype.card V * (2 * Fintype.card V / (d * (K + 1)) + 1) ∧
      ∀ i ∈ Q, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 4 := by
  classical
  obtain ⟨H₀, h₀G, h₀size, hdegree⟩ := exists_initialization G (3 * d)
  have hbase : H₀.edgeFinset.card ≤ 3 * Fintype.card V * d := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h₀size
  let M := fun i => missingIndices H₀ (p i)
  let A := P.filter fun i => (M i).card ≤ 2 * m
  let B := (P \ A).filter fun i => (M i).card ≤ K
  let C := (P \ A) \ B
  have hAP : A ⊆ P := filter_subset _ _
  have hBsub : B ⊆ P \ A := filter_subset _ _
  have hBP : B ⊆ P := hBsub.trans sdiff_subset
  have hCP : C ⊆ P := sdiff_subset.trans sdiff_subset
  have haCard := card_le_card hAP
  have hbCard := card_le_card hBP
  have hcCard := card_le_card hCP
  have htotal : A.card + B.card + C.card = P.card := by
    have ha := card_sdiff_add_card_eq_card hAP
    have hb := card_sdiff_add_card_eq_card hBsub
    change C.card + B.card = (P \ A).card at hb
    omega
  by_cases hA : P.card ≤ 3 * A.card
  · obtain ⟨H, hHG, hcost, hsat⟩ := exists_short_path_purchase G H₀ h₀G src dst p hp A (2 * m)
      (fun i hi => (mem_filter.mp hi).2)
    refine ⟨H, A, hHG, hAP, by omega, ?_, ?_⟩
    · have hm := Nat.mul_le_mul_right (2 * m) haCard
      have hc : H.edgeFinset.card ≤ 3 * Fintype.card V * d + 2 * P.card * m := by
        nlinarith only [hcost, hbase, hm]
      omega
    · intro i hi
      rw [hsat i hi]
      exact le_self_add
  · by_cases hB : P.card ≤ 3 * B.card
    · obtain ⟨H, Q, hHG, hQB, hhalf, hcost, hsat⟩ :=
        exists_plus_four_medium G H₀ h₀G src dst p hp B d m K hd hdegree (by
          intro i hi
          obtain ⟨hiPA, hiK⟩ := mem_filter.mp hi
          have hi' := mem_sdiff.mp hiPA
          refine ⟨?_, hiK⟩
          by_contra hn
          change ¬ 2 * m < (M i).card at hn
          exact hi'.2 (mem_filter.mpr ⟨hi'.1, by omega⟩))
      refine ⟨H, Q, hHG, hQB.trans hBP, by omega, ?_, hsat⟩
      have hm : 2 * B.card * m ≤ 2 * P.card * m := Nat.mul_le_mul_right m (Nat.mul_le_mul_left 2 hbCard)
      have hc := hcost.trans (Nat.add_le_add_right (Nat.add_le_add hbase hm)
        ((2 * (2 * Fintype.card V / (d * (m + 1)) + 1)) ^ 2 * K))
      omega
    · have hC : P.card ≤ 3 * C.card := by omega
      obtain ⟨H, Q, hHG, hQC, hhalf, hcost, hsat⟩ :=
        exists_long_path_purchase G H₀ h₀G src dst p hp C d K hd hdegree (by
          intro i hi
          obtain ⟨hiPA, hiB⟩ := mem_sdiff.mp hi
          by_contra hn
          change ¬ K < (M i).card at hn
          exact hiB (mem_filter.mpr ⟨hiPA, by omega⟩))
      refine ⟨H, Q, hHG, hQC.trans hCP, by omega, ?_, ?_⟩
      · nlinarith
      · intro i hi
        exact (hsat i hi).trans (add_le_add le_rfl (by norm_num))

end SlackSparsification
