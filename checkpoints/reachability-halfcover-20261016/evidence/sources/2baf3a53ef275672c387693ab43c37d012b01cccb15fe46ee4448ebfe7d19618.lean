import SlackSparsification.ReachabilityContracts
import Mathlib.Data.Nat.Sqrt

namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal BigOperators
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

/-- Buy all short paths and route a half-hit set of long paths through hubs.
Only allowed simple paths are used; optimal distances are not needed. -/
theorem reachability_integer_paths (K : SimpleGraph V) (A : V → V → Prop)
    (C : ℝ) (hC : 0 ≤ C) (hs : BidirectionalSourcewiseBound K A C)
    (src dst : D → V) (p : ∀ i, K.Walk (src i) (dst i))
    (hp : ∀ i, Allowed A (p i) ∧ (p i).IsPath) (P : Finset D) (l : ℕ) :
    ∃ (F : Finset (V × V)) (Q : Finset D), F ⊆ inputArcs K A ∧ Q ⊆ P ∧
      P.card ≤ 2 * Q.card ∧
      (F.card : ℝ) ≤ (P.card : ℝ) * l + 2 * C *
        (Real.sqrt (Fintype.card V * (P.card : ℝ) * (2 * Fintype.card V / (l + 1) + 1 : ℕ)) + Fintype.card V) ∧
      ∀ i ∈ Q, Reachable K (edgeRel F) (src i) (dst i) := by
  classical
  let B := P.filter fun i => (p i).length ≤ l
  let L := P \ B
  let N := fun i => (p i).support.toFinset
  have hN (i : D) (hi : i ∈ L) : l + 1 ≤ (N i).card := by
    have hlen : l < (p i).length := by
      obtain ⟨hiP, hiB⟩ := mem_sdiff.mp hi
      by_contra hn
      exact hiB (mem_filter.mpr ⟨hiP, by omega⟩)
    have hc : (N i).card = (p i).length + 1 := by
      rw [show N i = (p i).support.toFinset from rfl,
        List.toFinset_card_of_nodup (hp i).2.support_nodup, Walk.length_support]
    omega
  obtain ⟨S, Q₁, _, hSc, hQ₁L, hhalf, hhit⟩ := exists_half_hitting_set
    (univ : Finset V) univ_nonempty L N (l + 1) (by omega)
    (by intro i _; exact subset_univ _) hN
  choose r hrS hrN using hhit
  let mid := fun i => if hi : i ∈ Q₁ then r i hi else Classical.choice (inferInstance : Nonempty V)
  have hmid (i : D) (hi : i ∈ Q₁) : mid i ∈ S ∧ mid i ∈ (p i).support := by
    simp only [mid, dif_pos hi]
    exact ⟨hrS i hi, List.mem_toFinset.mp (hrN i hi)⟩
  have hroute : ∀ i ∈ Q₁, Reachable K A (src i) (dst i) →
      Reachable K A (src i) (mid i) ∧ Reachable K A (mid i) (dst i) := by
    intro i hi _
    have hm := (hmid i hi).2
    have ha : Allowed A ((p i).takeUntil (mid i) hm) ∧ Allowed A ((p i).dropUntil (mid i) hm) := by
      apply (allowed_append A _ _).mp
      rw [Walk.take_spec]
      exact (hp i).1
    exact ⟨⟨_,ha.1⟩,⟨_,ha.2⟩⟩
  obtain ⟨J, hJA, hJc, hJs⟩ := reachability_via_hubs hC hs S Q₁ src mid dst
    (fun i hi => (hmid i hi).1) hroute
  let T := B.biUnion fun i => arcs (p i)
  have hTA : ∀ e ∈ T, A e.1 e.2 := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact arcs_allowed (p i) (hp i).1 hi
  have hTc : T.card ≤ P.card * l := calc
    _ ≤ ∑ i ∈ B, (arcs (p i)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ B, l := sum_le_sum (fun i hi => (arcs_card_le (p i)).trans (mem_filter.mp hi).2)
    _ = B.card * l := by simp
    _ ≤ P.card * l := Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
  have hQP : Q₁ ⊆ P := hQ₁L.trans sdiff_subset
  have hcost : (J.card : ℝ) ≤ 2 * C *
      (Real.sqrt (Fintype.card V * (P.card : ℝ) * (2 * Fintype.card V / (l + 1) + 1 : ℕ)) + Fintype.card V) := by
    apply hJc.trans
    have hq : (Q₁.card : ℝ) ≤ P.card := by exact_mod_cast card_le_card hQP
    have hs' : (S.card : ℝ) ≤ (2 * Fintype.card V / (l+1) + 1 : ℕ) := by exact_mod_cast hSc
    gcongr
  let F := (T ∪ J).filter fun e => K.Adj e.1 e.2
  have hFA : F ⊆ inputArcs K A := by
    intro e he
    obtain ⟨he,hK⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨mem_univ _,hK,?_⟩
    rcases mem_union.mp he with he | he
    · exact hTA e he
    · exact (mem_filter.mp (hJA he)).2.2
  have hFc : (F.card : ℝ) ≤ (P.card : ℝ) * l + 2 * C *
      (Real.sqrt (Fintype.card V * (P.card : ℝ) * (2 * Fintype.card V / (l + 1) + 1 : ℕ)) + Fintype.card V) := by
    have h1 : (F.card : ℝ) ≤ (T ∪ J).card := by exact_mod_cast card_filter_le (T ∪ J) _
    have h2 : ((T ∪ J).card : ℝ) ≤ T.card + J.card := by exact_mod_cast card_union_le T J
    have h3 : (T.card : ℝ) ≤ (P.card : ℝ) * l := by exact_mod_cast hTc
    linarith
  have hBP : B ⊆ P := filter_subset _ _
  have hdis : Disjoint B Q₁ := disjoint_left.mpr (by
    intro i hi hi₁
    exact (mem_sdiff.mp (hQ₁L hi₁)).2 hi)
  refine ⟨F, B ∪ Q₁, hFA, union_subset hBP hQP, ?_, hFc, ?_⟩
  · have hc := card_sdiff_add_card_eq_card hBP
    have hq := card_union_of_disjoint hdis
    change L.card + B.card = P.card at hc
    omega
  · intro i hi
    apply (reachable_filter_ambient K (T ∪ J) _ _).mpr
    rcases mem_union.mp hi with hi | hi
    · refine ⟨p i, allowed_of_arcs (p i) ?_⟩
      intro e he
      exact mem_union_left _ (mem_biUnion.mpr ⟨i,hi,he⟩)
    · exact reachable_mono (fun _ _ h => mem_union_right T h)
        ((hJs i hi).mpr ⟨p i,(hp i).1⟩)

end SlackSparsification.Directed
