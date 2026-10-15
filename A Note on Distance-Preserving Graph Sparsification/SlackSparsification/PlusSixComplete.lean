import SlackSparsification.PlusSix
import SlackSparsification.PlusSixParameters
import Mathlib.Tactic

/-! Complete +6 spanners from actual finite constructions. Every graph endpoint retains the explicit uniform cited subset-spanner premise.
This does not certify that premise or the unconditional +6 application. -/
namespace SlackSparsification
open Finset SimpleGraph
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

/-- Conditional Theorem 11 with explicit uniform constant and the exponent 1/4. -/
theorem exists_plus_six_slack_rpow_paths (G : SimpleGraph V) (C : ℝ) (hC : 0 < C)
    (hsubset : UniformSubsetPlusTwo G C)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (hP : 0 < P.card) :
    ∃ (H : SimpleGraph V) (Q : Finset D), H ≤ G ∧ Q ⊆ P ∧
      P.card ≤ 4 * Q.card ∧
      (H.edgeFinset.card : ℝ) ≤ (10 + 6 * C) * Fintype.card V * (P.card : ℝ) ^ (1 / 4 : ℝ) ∧
      ∀ i ∈ Q, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 6 := by
  obtain ⟨k, hk, hPk, hkr⟩ := exists_fourth_parameter P.card hP
  obtain ⟨H, Q, hHG, hQP, hhalf, hcost, hsat⟩ :=
    exists_plus_six_slack_paths G C hC hsubset src dst p hp P k
      (Fintype.card V / k ^ 3) hk
  have hc := hcost.trans (plus_six_integer_budget (Fintype.card V) P.card k hk hPk C hC)
  refine ⟨H, Q, hHG, hQP, hhalf, ?_, hsat⟩
  have hm := mul_le_mul_of_nonneg_left hkr
    (show (0 : ℝ) ≤ (5 + 3 * C) * Fintype.card V by positivity)
  nlinarith

/-- Conditional Theorem 11 amplified for an arbitrary finite collection of actual shortest paths. -/
theorem exists_plus_six_complete_paths (G : SimpleGraph V) (C : ℝ) (hC : 0 < C)
    (hsubset : UniformSubsetPlusTwo G C)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i)) (P : Finset D) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (H.edgeFinset.card : ℝ) ≤
        ((10 + 6 * C) * Fintype.card V / (1 - (3 / 4 : ℝ) ^ (1 / 4 : ℝ))) *
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
        (R.card : ℝ) ≤ (3 / 4 : ℝ) * Q.card ∧
        (E.card : ℝ) ≤ ((10 + 6 * C) * Fintype.card V) * (Q.card : ℝ) ^ (1 / 4 : ℝ) ∧
        ∀ i ∈ Q \ R, Sat E i := by
    intro Q hQ
    obtain ⟨H, S, hHG, hSQ, hhalf, hcost, hsat⟩ :=
      exists_plus_six_slack_rpow_paths G C hC hsubset src dst p hp Q hQ
    refine ⟨H.edgeFinset, Q \ S, edgeFinset_mono hHG, sdiff_subset, ?_, hcost, ?_⟩
    · have hc := card_sdiff_add_card_eq_card hSQ
      have hc' : ((Q \ S).card : ℝ) + S.card = Q.card := by exact_mod_cast hc
      have hh : (Q.card : ℝ) ≤ 4 * S.card := by exact_mod_cast hhalf
      linarith
    · intro i hi
      have hiS : i ∈ S := by
        obtain ⟨hiQ, hiR⟩ := mem_sdiff.mp hi
        by_contra hn
        exact hiR (mem_sdiff.mpr ⟨hiQ, hn⟩)
      simpa [Sat] using hsat i hiS
  obtain ⟨E, hEG, hcost, hsat⟩ := complete_of_slack G.edgeFinset Sat hmono
    0 ((10 + 6 * C) * Fintype.card V) (3 / 4) (1 / 4) (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (by norm_num) 0 hsmall hslack P
  refine ⟨graphOfEdges E, graphOfEdges_le hEG, ?_, hsat⟩
  have hc : ((graphOfEdges E).edgeFinset.card : ℝ) ≤ E.card := by
    exact_mod_cast graphOfEdges_card_le E
  exact hc.trans (by simpa using hcost)

omit [Nonempty V] in
/-- Conditional Theorem 9, obtained by amplifying Theorem 11, including disconnected graphs and empty demand sets. The
explicit uniform constant is (10+6C)/(1-(3/4)^(1/4)), conditional on Theorem 10. -/
theorem exists_plus_six_complete (G : SimpleGraph V) (C : ℝ) (hC : 0 < C)
    (hsubset : UniformSubsetPlusTwo G C) (P : Finset (V × V)) :
    ∃ H : SimpleGraph V, IsAdditiveSpanner G H P 6 ∧
      (H.edgeFinset.card : ℝ) ≤
        ((10 + 6 * C) * Fintype.card V / (1 - (3 / 4 : ℝ) ^ (1 / 4 : ℝ))) *
          (P.card : ℝ) ^ (1 / 4 : ℝ) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    refine ⟨⊥, ⟨bot_le, ?_⟩, ?_⟩
    · intro st
      exact isEmptyElim st.1
    · simp
  | inr h =>
    let := h
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
