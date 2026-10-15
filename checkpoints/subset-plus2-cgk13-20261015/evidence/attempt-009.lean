import SlackSparsification.SubsetPlusTwoCore

/-! Finite rejection and charging contracts for CGK13. These do not assume
that the concrete clustering or purchase sequence has already been built. -/
namespace SlackSparsification.SubsetPlusTwo
open Finset
open scoped BigOperators

/-- A rejected path with cost at most twice its visited-cluster count has
a cluster improving neither endpoint. BL and BR refer to restricted path minima. -/
theorem exists_unimproved_cluster {A : Type*} [DecidableEq A]
    (Cs BL BR : Finset A) (cost : ℕ) (hcost : cost ≤ 2 * Cs.card)
    (hreject : 2 * (BL.card + BR.card) < cost) :
    ∃ c ∈ Cs, c ∉ BL ∧ c ∉ BR := by
  by_contra! hn
  have hsub : Cs ⊆ BL ∪ BR := by
    intro c hc
    by_cases h : c ∈ BL
    · exact mem_union_left _ h
    · exact mem_union_right _ (hn c hc h)
  have hcount := (card_le_card hsub).trans (card_union_le BL BR)
  omega

/-- Each successful purchase has a post-distance in a three-integer window.
Monotonicity and strict improvement force distinct post-distances, including
when the first pre-distance was infinite. -/
theorem improvement_card_le_three (T : Finset ℕ) (d : ℕ → ℕ∞) (b : ℕ)
    (hmono : Antitone d) (hstrict : ∀ i ∈ T, d (i + 1) < d i)
    (hlower : ∀ i ∈ T, (b : ℕ∞) ≤ d (i + 1))
    (hupper : ∀ i ∈ T, d (i + 1) ≤ (b : ℕ∞) + 2) : T.card ≤ 3 := by
  have hfin : ∀ i ∈ T, d (i + 1) ≠ ⊤ := by
    intro i hi
    exact ne_top_of_le_ne_top (by simp) (hupper i hi)
  let f := fun i => (d (i + 1)).toNat
  have hinj : Set.InjOn f (↑T : Set ℕ) := by
    intro i hi j hj he
    have heq : d (i + 1) = d (j + 1) := by
      rw [← ENat.natCast_toNat (hfin i hi), ← ENat.natCast_toNat (hfin j hj)]
      exact congrArg (fun n : ℕ => (n : ℕ∞)) he
    by_contra hn
    rcases lt_or_gt_of_ne hn with hij | hji
    · have h := (hstrict j hj).trans_le (hmono (show i + 1 ≤ j by omega))
      exact (ne_of_lt h) heq.symm
    · have h := (hstrict i hi).trans_le (hmono (show j + 1 ≤ i by omega))
      exact (ne_of_lt h) heq
  have hsub : T.image f ⊆ Icc b (b + 2) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hl := hlower i hi
    have hu := hupper i hi
    rw [← ENat.natCast_toNat (hfin i hi)] at hl hu
    have hl' : b ≤ f i := by exact_mod_cast hl
    have hu' : f i ≤ b + 2 := by exact_mod_cast hu
    exact mem_Icc.mpr ⟨hl', hu'⟩
  have h := card_le_card hsub
  rw [card_image_of_injOn hinj] at h
  simp only [Nat.card_Icc] at h
  omega

/-- Abstract accounting for the buy rule cost ≤ 2*value. A charge label
is a source/cluster pair; at most three improvements yields total cost ≤6|Q|. -/
theorem total_purchase_cost_le_six {I Q : Type*} [DecidableEq Q]
    (T : Finset I) (labels : Finset Q) (charge : I → Q → Prop)
    [DecidableRel charge] (cost : I → ℕ)
    (haffordable : ∀ i ∈ T, cost i ≤ 2 * (labels.filter (charge i)).card)
    (hthree : ∀ q ∈ labels, (T.filter fun i => charge i q).card ≤ 3) :
    ∑ i ∈ T, cost i ≤ 6 * labels.card := by
  have hdouble : (∑ i ∈ T, (labels.filter (charge i)).card) =
      ∑ q ∈ labels, (T.filter fun i => charge i q).card := by
    simp only [card_eq_sum_ones, sum_filter]
    exact sum_comm
  calc
    _ ≤ ∑ i ∈ T, 2 * (labels.filter (charge i)).card := sum_le_sum haffordable
    _ = 2 * ∑ q ∈ labels, (T.filter fun i => charge i q).card := by
      rw [← mul_sum, hdouble]
    _ ≤ 2 * ∑ _q ∈ labels, 3 := Nat.mul_le_mul_left _ (sum_le_sum hthree)
    _ = 6 * labels.card := by simp; omega

end SlackSparsification.SubsetPlusTwo
