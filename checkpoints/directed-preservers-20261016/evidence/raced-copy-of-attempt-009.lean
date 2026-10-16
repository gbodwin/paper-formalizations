import SlackSparsification.DirectedExact
import SlackSparsification.Amplification
import Mathlib.Tactic

/-! Theorem 3: complete finite directed nonnegative-weight distance
preservers with O(n sqrt(p)) arcs, including unreachable and empty demands. -/
namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped ENNReal NNReal
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

/-- A rounded square root has both the combinatorial and analytic bounds
needed by the construction. -/
theorem exists_square_parameter (p : ℕ) (hp : 0 < p) :
    ∃ k : ℕ, 0 < k ∧ p ≤ k ^ 2 ∧ (k : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 2 : ℝ) := by
  let r : ℝ := (p : ℝ) ^ (1 / 2 : ℝ)
  have hr : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ p by omega)) (by norm_num)
  have hr0 : 0 ≤ r := by linarith
  let k := ⌈r⌉₊
  have hkr : r ≤ (k : ℝ) := Nat.le_ceil r
  have hkle : (k : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
  have hk : 0 < k := by
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  have hcube : r ^ 2 = (p : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hpc : p ≤ k ^ 2 := by
    have h := pow_le_pow_left₀ hr0 hkr 2
    rw [hcube] at h
    exact_mod_cast h
  exact ⟨k, hk, hpc, by linarith⟩


theorem exists_exact_slack_rpow_paths (K : SimpleGraph V) (A : V → V → Prop) (w : V → V → ℝ≥0)
    (src dst : D → V) (p : ∀ i, K.Walk (src i) (dst i)) (hp : ∀ i, Optimal A w (p i))
    (P : Finset D) (hP : 0 < P.card) :
    ∃ (F : Finset (V × V)) (Q : Finset D), (∀ e ∈ F, A e.1 e.2) ∧ Q ⊆ P ∧ P.card ≤ 2 * Q.card ∧
      (F.card : ℝ) ≤ 14 * Fintype.card V * (P.card : ℝ) ^ (1 / 2 : ℝ) ∧
      ∀ i ∈ Q, distance K (edgeRel F) w (src i) (dst i) = distance K A w (src i) (dst i) := by
  obtain ⟨k, hk, hPk, hkr⟩ := exists_square_parameter P.card hP
  obtain ⟨F, Q, hFA, hQP, hhalf, hcost, hsat⟩ :=
    exists_exact_slack_paths K A w src dst p hp P (Fintype.card V / k)
  have hc := hcost.trans (exact_integer_budget (Fintype.card V) P.card k hk hPk)
  refine ⟨F, Q, hFA, hQP, hhalf, ?_, hsat⟩
  have hc' : (F.card : ℝ) ≤ 7 * Fintype.card V * k := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hkr (show (0 : ℝ) ≤ 7 * Fintype.card V by positivity)
  nlinarith

theorem exists_exact_complete_paths (K : SimpleGraph V) (A : V → V → Prop) (w : V → V → ℝ≥0)
    (src dst : D → V) (p : ∀ i, K.Walk (src i) (dst i)) (hp : ∀ i, Optimal A w (p i))
    (P : Finset D) :
    ∃ F : Finset (V × V), (∀ e ∈ F, A e.1 e.2) ∧
      (F.card : ℝ) ≤ (14 * Fintype.card V / (1 - (1 / 2 : ℝ) ^ (1 / 2 : ℝ))) *
        (P.card : ℝ) ^ (1 / 2 : ℝ) ∧
      ∀ i ∈ P, distance K (edgeRel F) w (src i) (dst i) = distance K A w (src i) (dst i) := by
  classical
  let U := (univ : Finset (V × V)).filter fun e => A e.1 e.2
  let Sat := fun (F : Finset (V × V)) i => distance K (edgeRel F) w (src i) (dst i) ≤ distance K A w (src i) (dst i)
  have hmono : ∀ F J, F ⊆ J → ∀ i, Sat F i → Sat J i := by
    intro F J hFJ i hi
    exact (distance_mono w (fun _ _ h => hFJ h) _ _).trans hi
  have hsmall : ∀ Q : Finset D, Q.card ≤ 0 →
      ∃ F : Finset (V × V), F ⊆ U ∧ (F.card : ℝ) ≤ 0 ∧ ∀ i ∈ Q, Sat F i := by
    intro Q hQ
    have he : Q = ∅ := card_eq_zero.mp (by omega)
    exact ⟨∅, empty_subset _, by simp, by simp [he]⟩
  have hslack : ∀ Q : Finset D, 0 < Q.card →
      ∃ (F : Finset (V × V)) (R : Finset D), F ⊆ U ∧ R ⊆ Q ∧
        (R.card : ℝ) ≤ (1 / 2 : ℝ) * Q.card ∧
        (F.card : ℝ) ≤ (14 * Fintype.card V) * (Q.card : ℝ) ^ (1 / 2 : ℝ) ∧
        ∀ i ∈ Q \ R, Sat F i := by
    intro Q hQ
    obtain ⟨F, S, hFA, hSQ, hhalf, hcost, hsat⟩ := exists_exact_slack_rpow_paths K A w src dst p hp Q hQ
    refine ⟨F, Q \ S, ?_, sdiff_subset, ?_, hcost, ?_⟩
    · intro e he
      exact mem_filter.mpr ⟨mem_univ _, hFA e he⟩
    · have hc := card_sdiff_add_card_eq_card hSQ
      have hc' : ((Q \ S).card : ℝ) + S.card = Q.card := by exact_mod_cast hc
      have hh : (Q.card : ℝ) ≤ 2 * S.card := by exact_mod_cast hhalf
      linarith
    · intro i hi
      have hiS : i ∈ S := by
        obtain ⟨hiQ, hiR⟩ := mem_sdiff.mp hi
        by_contra hn
        exact hiR (mem_sdiff.mpr ⟨hiQ, hn⟩)
      exact (hsat i hiS).le
  obtain ⟨F, hFU, hcost, hsat⟩ := complete_of_slack U Sat hmono
    0 (14 * Fintype.card V) (1 / 2) (1 / 2) (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (by norm_num) 0 hsmall hslack P
  have hFA : ∀ e ∈ F, A e.1 e.2 := fun e he => (mem_filter.mp (hFU he)).2
  refine ⟨F, hFA, by simpa using hcost, ?_⟩
  intro i hi
  exact le_antisymm (hsat i hi) (distance_mono w (fun u v h => hFA (u,v) h) _ _)

/- Theorem 3, with actual directed arcs and actual nonnegative-weight distances. -/
omit [Nonempty V] in
theorem exists_exact_complete (K : SimpleGraph V) (A : V → V → Prop) (w : V → V → ℝ≥0)
    (P : Finset (V × V)) :
    ∃ F : Finset (V × V), (∀ e ∈ F, A e.1 e.2) ∧
      (F.card : ℝ) ≤ (14 * Fintype.card V / (1 - (1 / 2 : ℝ) ^ (1 / 2 : ℝ))) *
        (P.card : ℝ) ^ (1 / 2 : ℝ) ∧
      ∀ st ∈ P, distance K (edgeRel F) w st.1 st.2 = distance K A w st.1 st.2 := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    refine ⟨∅, by simp, by simp, ?_⟩
    intro st
    exact isEmptyElim st.1
  | inr h =>
    letI := h
    let DR := {st : V × V // ∃ p : K.Walk st.1 st.2, Allowed A p}
    let Q : Finset DR := P.subtype fun st => ∃ p : K.Walk st.1 st.2, Allowed A p
    choose p hp using fun i : DR => exists_optimal A w i.val.1 i.val.2 i.property
    obtain ⟨F, hFA, hcost, hsat⟩ := exists_exact_complete_paths K A w
      (fun i : DR => i.val.1) (fun i : DR => i.val.2) p hp Q
    refine ⟨F, hFA, ?_, ?_⟩
    · apply hcost.trans
      have hQ : Q.card ≤ P.card :=
        (Finset.card_subtype (fun st => ∃ p : K.Walk st.1 st.2, Allowed A p) P).trans_le (card_filter_le _ _)
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
        (show (Q.card : ℝ) ≤ P.card by exact_mod_cast hQ) (by norm_num))
      exact div_nonneg (by positivity) (le_of_lt (sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num))))
    · intro st hst
      by_cases hr : ∃ p : K.Walk st.1 st.2, Allowed A p
      · exact hsat ⟨st, hr⟩ (Finset.mem_subtype.mpr hst)
      · apply le_antisymm _ (distance_mono w (fun u v h => hFA (u,v) h) _ _)
        simp [distance_of_no_walk w hr]

end SlackSparsification.Directed
