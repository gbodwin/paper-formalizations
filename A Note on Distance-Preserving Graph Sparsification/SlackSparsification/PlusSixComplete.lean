import SlackSparsification.PlusSix
import SlackSparsification.PlusSixParameters
import SlackSparsification.PathPurchases
import Mathlib.Tactic

/-! Theorems 9 and 11 relative to their stated external input (Theorem 10).
No claim is made that the cited subset-spanner theorem is formalized here. -/
namespace SlackSparsification
open Finset SimpleGraph
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

theorem exists_plus_six_slack_rpow_paths (G : SimpleGraph V)
    (C : ℝ) (hC : 0 ≤ C) (hsubset : SubsetTwoBound G C)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (hP : 0 < P.card) :
    ∃ (H : SimpleGraph V) (Q : Finset D), H ≤ G ∧ Q ⊆ P ∧ P.card ≤ 8 * Q.card ∧
      (H.edgeFinset.card : ℝ) ≤ (10 + 6 * C) * Fintype.card V * (P.card : ℝ) ^ (1 / 4 : ℝ) ∧
      ∀ i ∈ Q, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 6 := by
  classical
  obtain ⟨k, hk, hPk, hkr⟩ := exists_fourth_parameter P.card hP
  let n := Fintype.card V
  let m := n / k ^ 3
  let L : ℝ := C * n * Real.sqrt (2 * (2 * n / (k * (m + 1)) + 1) : ℕ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbudget : ((3 * n * k + 2 * P.card * m : ℕ) : ℝ) + L ≤ (5 + 3 * C) * n * k :=
    plus_six_integer_budget n P.card k hk hPk C hC
  have hfinal : (5 + 3 * C) * n * k ≤ (10 + 6 * C) * n * (P.card : ℝ) ^ (1 / 4 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hkr (show (0 : ℝ) ≤ (5 + 3 * C) * n by positivity)
    nlinarith
  obtain ⟨H₀, h₀G, h₀size, hdegree⟩ := exists_initialization G (3 * k)
  have hbase : (H₀.edgeFinset.card : ℝ) ≤ 3 * n * k := by
    exact_mod_cast (show H₀.edgeFinset.card ≤ 3 * n * k by simpa [n, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h₀size)
  let A := P.filter fun i => (missingIndices H₀ (p i)).card ≤ 2 * m
  let B := P \ A
  have hAP : A ⊆ P := filter_subset _ _
  have hBP : B ⊆ P := sdiff_subset
  have hac := card_le_card hAP
  have hbc := card_le_card hBP
  have hsum := card_sdiff_add_card_eq_card hAP
  change B.card + A.card = P.card at hsum
  by_cases hA : P.card ≤ 2 * A.card
  · obtain ⟨H, hHG, hcost, hsat⟩ := exists_short_path_purchase G H₀ h₀G src dst p hp A (2 * m)
      (fun i hi => (mem_filter.mp hi).2)
    refine ⟨H, A, hHG, hAP, by omega, ?_, ?_⟩
    · apply le_trans _ (hbudget.trans hfinal)
      have hc : (H.edgeFinset.card : ℝ) ≤ H₀.edgeFinset.card + A.card * (2 * m) := by exact_mod_cast hcost
      have hm : (A.card : ℝ) * m ≤ P.card * m := by exact_mod_cast Nat.mul_le_mul_right m hac
      push_cast
      nlinarith
    · intro i hi
      rw [hsat i hi]
      exact le_self_add
  · obtain ⟨H, Q, hHG, hQB, hhalf, hcost, hsat⟩ :=
      exists_plus_six_long_of_subset G H₀ h₀G src dst p hp B k m hk C hC hsubset hdegree (by
        intro i hi
        obtain ⟨hiP, hiA⟩ := mem_sdiff.mp hi
        by_contra hn
        exact hiA (mem_filter.mpr ⟨hiP, by omega⟩))
    refine ⟨H, Q, hHG, hQB.trans hBP, by omega, ?_, hsat⟩
    apply le_trans _ (hbudget.trans hfinal)
    have hm : (B.card : ℝ) * m ≤ P.card * m := by exact_mod_cast Nat.mul_le_mul_right m hbc
    change (H.edgeFinset.card : ℝ) ≤ H₀.edgeFinset.card + 2 * B.card * m + L at hcost
    push_cast
    nlinarith

/-- Theorem 9 (relative to Theorem 10) for an arbitrary finite collection of actual shortest paths. -/
theorem exists_plus_six_complete_paths (G : SimpleGraph V)
    (C : ℝ) (hC : 0 ≤ C) (hsubset : SubsetTwoBound G C)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i)) (P : Finset D) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (H.edgeFinset.card : ℝ) ≤
        ((10 + 6 * C) * Fintype.card V / (1 - (7 / 8 : ℝ) ^ (1 / 4 : ℝ))) *
          (P.card : ℝ) ^ (1 / 4 : ℝ) ∧
      ∀ i ∈ P, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 6 := by
  classical
  let Sat := fun (E : Finset (Sym2 V)) i =>
    (graphOfEdges E).edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 6
  have hmono : ∀ E F, E ⊆ F → ∀ i, Sat E i → Sat F i := by
    intro E F hEF i hi
    exact (edist_anti (graphOfEdges_mono hEF)).trans hi
  have hsmall : ∀ Q : Finset D, Q.card ≤ 0 →
      ∃ E : Finset (Sym2 V), E ⊆ G.edgeFinset ∧ (E.card : ℝ) ≤ 0 ∧ ∀ i ∈ Q, Sat E i := by
    intro Q hQ
    have he : Q = ∅ := card_eq_zero.mp (by omega)
    exact ⟨∅, empty_subset _, by simp, by simp [he]⟩
  have hslack : ∀ Q : Finset D, 0 < Q.card →
      ∃ (E : Finset (Sym2 V)) (R : Finset D), E ⊆ G.edgeFinset ∧ R ⊆ Q ∧
        (R.card : ℝ) ≤ (7 / 8 : ℝ) * Q.card ∧
        (E.card : ℝ) ≤ ((10 + 6 * C) * Fintype.card V) * (Q.card : ℝ) ^ (1 / 4 : ℝ) ∧
        ∀ i ∈ Q \ R, Sat E i := by
    intro Q hQ
    obtain ⟨H, S, hHG, hSQ, hhalf, hcost, hsat⟩ :=
      exists_plus_six_slack_rpow_paths G C hC hsubset src dst p hp Q hQ
    refine ⟨H.edgeFinset, Q \ S, edgeFinset_mono hHG, sdiff_subset, ?_, hcost, ?_⟩
    · have hc := card_sdiff_add_card_eq_card hSQ
      have hc' : ((Q \ S).card : ℝ) + S.card = Q.card := by exact_mod_cast hc
      have hh : (Q.card : ℝ) ≤ 8 * S.card := by exact_mod_cast hhalf
      linarith
    · intro i hi
      have hiS : i ∈ S := by
        obtain ⟨hiQ, hiR⟩ := mem_sdiff.mp hi
        by_contra hn
        exact hiR (mem_sdiff.mpr ⟨hiQ, hn⟩)
      simpa [Sat] using hsat i hiS
  obtain ⟨E, hEG, hcost, hsat⟩ := complete_of_slack G.edgeFinset Sat hmono
    0 ((10 + 6 * C) * Fintype.card V) (7 / 8) (1 / 4) (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (by norm_num) 0 hsmall hslack P
  refine ⟨graphOfEdges E, graphOfEdges_le hEG, ?_, hsat⟩
  have hc : ((graphOfEdges E).edgeFinset.card : ℝ) ≤ E.card := by
    exact_mod_cast graphOfEdges_card_le E
  exact hc.trans (by simpa using hcost)

/- Theorem 9 (relative to Theorem 10), including disconnected graphs and empty demand sets. The
explicit uniform constant is (10 + 6 * C)/(1 - (7/8)^(1/4)). -/
omit [Nonempty V] in
theorem exists_plus_six_complete (G : SimpleGraph V) (P : Finset (V × V))
    (C : ℝ) (hC : 0 ≤ C) (hsubset : SubsetTwoBound G C) :
    ∃ H : SimpleGraph V, IsAdditiveSpanner G H P 6 ∧
      (H.edgeFinset.card : ℝ) ≤
        ((10 + 6 * C) * Fintype.card V / (1 - (7 / 8 : ℝ) ^ (1 / 4 : ℝ))) *
          (P.card : ℝ) ^ (1 / 4 : ℝ) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    refine ⟨⊥, ⟨bot_le, ?_⟩, ?_⟩
    · intro st
      exact isEmptyElim st.1
    · simp
  | inr h =>
    letI := h
    let DR := {st : V × V // G.Reachable st.1 st.2}
    let Q : Finset DR := P.subtype fun st => G.Reachable st.1 st.2
    choose p hp using fun i : DR => i.property.exists_walk_length_eq_dist
    obtain ⟨H, hHG, hcost, hsat⟩ := exists_plus_six_complete_paths G C hC hsubset
      (fun i : DR => i.val.1) (fun i : DR => i.val.2) p hp Q
    refine ⟨H, ⟨hHG, ?_⟩, ?_⟩
    · intro st hst
      by_cases hr : G.Reachable st.1 st.2
      · exact hsat ⟨st, hr⟩ (Finset.mem_subtype.mpr hst)
      · simp [edist_eq_top_of_not_reachable hr]
    · apply hcost.trans
      have hQ : Q.card ≤ P.card := by
        exact (Finset.card_subtype (fun st => G.Reachable st.1 st.2) P).trans_le (card_filter_le _ _)
      have hpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ Q.card by positivity)
        (show (Q.card : ℝ) ≤ P.card by exact_mod_cast hQ) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      apply mul_le_mul_of_nonneg_left hpow
      apply div_nonneg (by positivity)
      exact le_of_lt (sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)))

end SlackSparsification
