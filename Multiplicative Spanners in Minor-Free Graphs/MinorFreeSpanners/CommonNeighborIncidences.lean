import MinorFreeSpanners.MateFreeSets
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact double counting of ordered distinct leaf pairs through their real
common neighbors. This supplies collision budgets from mate-freeness. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Literal ordered pairs in one neighbor slice are the corresponding
filtered ordered leaf pairs. -/
theorem neighbor_slice_offDiag (G : SimpleGraph V) (S : Finset V) (z : V) :
    (S.filter fun x => G.Adj x z).offDiag =
      S.offDiag.filter fun p => G.Adj p.1 z ∧ G.Adj p.2 z := by
  classical
  ext p
  simp only [Finset.mem_offDiag,Finset.mem_filter]
  tauto

/-- Count exactly the same ordered-pair/common-neighbor triples in both
orders, without replacing actual graph incidence by a numerical premise. -/
theorem ordered_pair_common_neighbor_sum (G : SimpleGraph V) (S : Finset V) :
    (∑ z : V, (S.filter fun x => G.Adj x z).card *
      ((S.filter fun x => G.Adj x z).card-1)) =
    ∑ p ∈ S.offDiag, Fintype.card (G.commonNeighbors p.1 p.2) := by
  classical
  have hs (z : V) : (S.filter fun x => G.Adj x z).card *
        ((S.filter fun x => G.Adj x z).card-1) =
      ∑ p ∈ S.offDiag, if G.Adj p.1 z ∧ G.Adj p.2 z then 1 else 0 := by
    rw [Nat.mul_sub_left_distrib,Nat.mul_one,← Finset.offDiag_card,
      neighbor_slice_offDiag,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have he : (Finset.univ.filter fun z => G.Adj p.1 z ∧ G.Adj p.2 z) =
      (G.commonNeighbors p.1 p.2).toFinset := by
    ext z
    simp [SimpleGraph.mem_commonNeighbors]
  rw [← Finset.sum_filter,← Finset.card_eq_sum_ones,he,Set.toFinset_card]

/-- Mate-free leaves bound the actual total number of ordered collision
witnesses. The factor is exactly |S|*(|S|-1). -/
theorem MateFreeOn.ordered_collision_budget (G : SimpleGraph V) (S : Finset V)
    (q : ℝ) (h : MateFreeOn G q (S:Set V)) :
    ((∑ z : V, (S.filter fun x => G.Adj x z).card *
      ((S.filter fun x => G.Adj x z).card-1) : ℕ):ℝ) ≤
      (S.card*(S.card-1):ℕ)*q := by
  classical
  rw [ordered_pair_common_neighbor_sum]
  push_cast
  calc
    _ ≤ ∑ _p ∈ S.offDiag, q := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hx,hy,hxy⟩ := Finset.mem_offDiag.mp hp
      exact (h p.1 hx p.2 hy hxy).le
    _ = (S.offDiag.card:ℝ)*q := by simp
    _ = _ := by
      have hc : S.offDiag.card = S.card*(S.card-1) := by
        rw [Finset.offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one]
      rw [hc,Nat.cast_mul]

end MinorFreeSpanners
