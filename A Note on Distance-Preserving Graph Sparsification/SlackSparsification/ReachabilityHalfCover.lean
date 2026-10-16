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
    simp only [mid, dite_eq_left hi]
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


set_option maxHeartbeats 800000 in
/-- Unreachable demands are satisfied automatically and never placed in the
residual. Reachable demands receive internally chosen allowed simple paths. -/
theorem reachability_integer (K : SimpleGraph V) (A : V → V → Prop)
    (C : ℝ) (hC : 0 ≤ C) (hs : BidirectionalSourcewiseBound K A C)
    (P : Finset (V × V)) (l : ℕ) :
    ∃ (F R : Finset (V × V)), F ⊆ inputArcs K A ∧ R ⊆ P ∧
      (R.card : ℝ) ≤ (1/2 : ℝ) * P.card ∧
      (F.card : ℝ) ≤ (P.card : ℝ) * l + 2 * C *
        (Real.sqrt (Fintype.card V * (P.card : ℝ) * (2 * Fintype.card V / (l + 1) + 1 : ℕ)) + Fintype.card V) ∧
      ∀ st ∈ P \ R, Reachable K A st.1 st.2 → Reachable K (edgeRel F) st.1 st.2 := by
  classical
  let DR := {st : V × V // Reachable K A st.1 st.2}
  let Q : Finset DR := P.subtype fun st => Reachable K A st.1 st.2
  choose p hp using fun i : DR => exists_optimal A (fun _ _ => 0) i.val.1 i.val.2 i.property
  obtain ⟨F,S,hFA,hSQ,hhalf,hcost,hsat⟩ := reachability_integer_paths K A C hC hs
    (fun i : DR => i.val.1) (fun i : DR => i.val.2) p (fun i => ⟨(hp i).1,(hp i).2.1⟩) Q l
  let R := (Q \ S).image Subtype.val
  have hQc : Q.card ≤ P.card :=
    (Finset.card_subtype (fun st => Reachable K A st.1 st.2) P).trans_le (card_filter_le _ _)
  have hRP : R ⊆ P := by
    intro st hst
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hst
    exact Finset.mem_subtype.mp (mem_sdiff.mp hi).1
  refine ⟨F,R,hFA,hRP,?_,?_,?_⟩
  · have hc := card_sdiff_add_card_eq_card hSQ
    have hr : R.card ≤ (Q \ S).card := card_image_le
    have hh : 2 * R.card ≤ P.card := by omega
    have hh' : 2 * (R.card : ℝ) ≤ P.card := by exact_mod_cast hh
    linarith
  · apply hcost.trans
    have hq : (Q.card : ℝ) ≤ P.card := by exact_mod_cast hQc
    gcongr
  · intro st hst hr
    have hiQ : (⟨st,hr⟩ : DR) ∈ Q := Finset.mem_subtype.mpr (mem_sdiff.mp hst).1
    have hiS : (⟨st,hr⟩ : DR) ∈ S := by
      by_contra hn
      exact (mem_sdiff.mp hst).2 (mem_image.mpr ⟨⟨st,hr⟩,mem_sdiff.mpr ⟨hiQ,hn⟩,rfl⟩)
    exact hsat ⟨st,hr⟩ hiS

omit [Nonempty V] in
/-- The half-cover constructor is discharged from the two oriented sourcewise
premises. The integer cutoff is optimized only after constructing actual arcs. -/
theorem reachability_half_cover (K : SimpleGraph V) (A : V → V → Prop)
    (C : ℝ) (hC : 0 ≤ C) (hs : BidirectionalSourcewiseBound K A C) :
    ReachabilityHalfCover K A ((1 + 6*C) * (Fintype.card V : ℝ) ^ (2/3 : ℝ))
      (Nat.sqrt (Fintype.card V)) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    intro P _
    refine ⟨∅,∅,empty_subset _,empty_subset _,by simp,?_,?_⟩
    · simp
    · intro st
      exact isEmptyElim st.1
  | inr h =>
    let := h
    intro P hP
    have hn : 0 < Fintype.card V := Fintype.card_pos
    have hp : 0 < P.card := lt_of_le_of_lt (Nat.zero_le _) hP
    have hlarge : Fintype.card V < P.card ^ 2 := Nat.sqrt_lt'.mp hP
    obtain ⟨l,hbudget⟩ := reachability_slack_budget (Fintype.card V) P.card hn hp hlarge.le C hC
    obtain ⟨F,R,hFA,hRP,hhalf,hcost,hsat⟩ := reachability_integer K A C hC hs P l
    exact ⟨F,R,hFA,hRP,hhalf,hcost.trans hbudget,hsat⟩

omit [Nonempty V] in
/-- Complete reachability with only the two oriented sourcewise premises.
In particular, no half-cover, paths, hitting sets or trees are hypotheses. -/
theorem reachability_complete_sourcewise (K : SimpleGraph V) (A : V → V → Prop)
    (C : ℝ) (hC : 0 ≤ C) (hs : BidirectionalSourcewiseBound K A C)
    (P : Finset (V × V)) :
    ∃ F : Finset (V × V), F ⊆ inputArcs K A ∧
      (F.card : ℝ) ≤ 2 * C * Fintype.card V +
        ((1 + 6*C) * (Fintype.card V : ℝ) ^ (2/3 : ℝ)) /
          (1 - (1/2 : ℝ) ^ (2/3 : ℝ)) * (P.card : ℝ) ^ (2/3 : ℝ) ∧
      ∀ st ∈ P, (Reachable K (edgeRel F) st.1 st.2 ↔ Reachable K A st.1 st.2) := by
  apply reachability_complete_of_constructors K A C _ hC (by positivity)
    (Nat.sqrt (Fintype.card V)) (Nat.sqrt_le' _) hs.1
    (reachability_half_cover K A C hC hs) P

end SlackSparsification.Directed
