import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! A deterministic substitute for the constant-probability hitting step.
All sets, sampled vertices, covered demands and cardinalities are constructed.
No probabilistic independence assumptions or supplied favorable sample occur. -/
namespace SlackSparsification
open Finset
open scoped BigOperators
variable {V D : Type*} [DecidableEq V] [DecidableEq D]

def hits (P : Finset D) (N : D → Finset V) (v : V) : Finset D :=
  P.filter fun i => v ∈ N i

theorem hits_subset (P : Finset D) (N : D → Finset V) (v : V) :
    hits P N v ⊆ P := filter_subset _ _

/-- Exact double counting of a finite neighborhood incidence relation. -/
theorem sum_hits (U : Finset V) (P : Finset D) (N : D → Finset V)
    (hN : ∀ i ∈ P, N i ⊆ U) :
    ∑ v ∈ U, (hits P N v).card = ∑ i ∈ P, (N i).card := by
  classical
  calc
    _ = ∑ v ∈ U, ∑ i ∈ P, if v ∈ N i then 1 else 0 := by
      simp only [hits, card_eq_sum_ones, sum_filter]
    _ = ∑ i ∈ P, ∑ v ∈ U, if v ∈ N i then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      have heq : U.filter (fun v => v ∈ N i) = N i := by
        ext v
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hN i hi h, h⟩⟩
      rw [← sum_filter, ← card_eq_sum_ones, heq]

/-- One vertex hits at least the average number of demands. -/
theorem exists_popular_vertex (U : Finset V) (hU : U.Nonempty)
    (P : Finset D) (N : D → Finset V) (d : ℕ)
    (hN : ∀ i ∈ P, N i ⊆ U) (hd : ∀ i ∈ P, d ≤ (N i).card) :
    ∃ v ∈ U, d * P.card ≤ U.card * (hits P N v).card := by
  obtain ⟨v, hv, hmax⟩ := exists_max_image U (fun v => (hits P N v).card) hU
  refine ⟨v, hv, ?_⟩
  calc
    _ = ∑ _ ∈ P, d := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ P, (N i).card := sum_le_sum hd
    _ = ∑ u ∈ U, (hits P N u).card := (sum_hits U P N hN).symm
    _ ≤ ∑ _ ∈ U, (hits P N v).card := sum_le_sum hmax
    _ = _ := by simp

/-- The greedy construction after an arbitrary number of iterations. Once
half the demands are covered it stops. Otherwise a quantitative progress
invariant records the number removed. -/
theorem greedy_hitting_progress (U : Finset V) (hU : U.Nonempty)
    (P : Finset D) (N : D → Finset V) (d : ℕ)
    (hN : ∀ i ∈ P, N i ⊆ U) (hd : ∀ i ∈ P, d ≤ (N i).card)
    (t : ℕ) :
    ∃ (S : Finset V) (R : Finset D), S ⊆ U ∧ S.card ≤ t ∧ R ⊆ P ∧
      (∀ i ∈ P \ R, ∃ v ∈ S, v ∈ N i) ∧
      (2 * R.card ≤ P.card ∨ t * d * P.card ≤ 2 * U.card * (P.card - R.card)) := by
  induction t with
  | zero =>
    refine ⟨∅, P, empty_subset _, by simp, subset_rfl, ?_, Or.inr ?_⟩
    · simp
    · simp
  | succ t ih =>
    obtain ⟨S, R, hSU, hSt, hRP, hcover, hinv⟩ := ih
    by_cases hhalf : 2 * R.card ≤ P.card
    · exact ⟨S, R, hSU, by omega, hRP, hcover, Or.inl hhalf⟩
    · have hprogress := hinv.resolve_left hhalf
      obtain ⟨v, hvU, hv⟩ := exists_popular_vertex U hU R N d
        (fun i hi => hN i (hRP hi)) (fun i hi => hd i (hRP hi))
      let T := hits R N v
      have hTR : T ⊆ R := hits_subset R N v
      have hRcard : R.card ≤ P.card := card_le_card hRP
      have hTcard : (R \ T).card + T.card = R.card := card_sdiff_add_card_eq_card hTR
      have hstep : d * P.card ≤ 2 * U.card * T.card := by
        have h := Nat.mul_le_mul_left d (show P.card ≤ 2 * R.card by omega)
        change d * R.card ≤ U.card * T.card at hv
        nlinarith
      refine ⟨insert v S, R \ T, insert_subset hvU hSU, ?_,
        (sdiff_subset).trans hRP, ?_, Or.inr ?_⟩
      · exact (card_insert_le v S).trans (by omega)
      · intro i hi
        obtain ⟨hiP, hiR⟩ := mem_sdiff.mp hi
        by_cases hir : i ∈ R
        · have hit : i ∈ T := by
            by_contra hn
            exact hiR (mem_sdiff.mpr ⟨hir, hn⟩)
          exact ⟨v, mem_insert_self _ _, (mem_filter.mp hit).2⟩
        · obtain ⟨u, huS, huN⟩ := hcover i (mem_sdiff.mpr ⟨hiP, hir⟩)
          exact ⟨u, mem_insert_of_mem huS, huN⟩
      · have hRnew : (R \ T).card ≤ R.card := card_le_card sdiff_subset
        have hsub : P.card - (R \ T).card = (P.card - R.card) + T.card := by omega
        rw [hsub]
        nlinarith

/-- A small set of vertices hits at least half the demand neighborhoods.
The cost is at most `floor(2|U|/d)+1`, with no logarithmic factor. -/
theorem exists_half_hitting_set (U : Finset V) (hU : U.Nonempty)
    (P : Finset D) (N : D → Finset V) (d : ℕ) (hd0 : 0 < d)
    (hN : ∀ i ∈ P, N i ⊆ U) (hd : ∀ i ∈ P, d ≤ (N i).card) :
    ∃ (S : Finset V) (Q : Finset D), S ⊆ U ∧ S.card ≤ 2 * U.card / d + 1 ∧
      Q ⊆ P ∧ P.card ≤ 2 * Q.card ∧ ∀ i ∈ Q, ∃ v ∈ S, v ∈ N i := by
  obtain ⟨S, R, hSU, hSc, hRP, hcover, hinv⟩ :=
    greedy_hitting_progress U hU P N d hN hd (2 * U.card / d + 1)
  have hRcard := card_le_card hRP
  have hhalf : 2 * R.card ≤ P.card := by
    rcases hinv with h | h
    · exact h
    · by_contra hnot
      have hp : 0 < P.card := by omega
      have hdiv : 2 * U.card < (2 * U.card / d + 1) * d :=
        by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ (2 * U.card) hd0
      have hle : P.card - R.card ≤ P.card := Nat.sub_le _ _
      nlinarith
  refine ⟨S, P \ R, hSU, hSc, sdiff_subset, ?_, hcover⟩
  have h := card_sdiff_add_card_eq_card hRP
  omega

/-- Two independently constructed root sets hit both neighborhoods of at
least one quarter of the demands; their union has an explicit size bound. -/
theorem exists_two_sided_hitting_set (U : Finset V) (hU : U.Nonempty)
    (P : Finset D) (N₁ N₂ : D → Finset V) (d : ℕ) (hd0 : 0 < d)
    (hN₁ : ∀ i ∈ P, N₁ i ⊆ U) (hN₂ : ∀ i ∈ P, N₂ i ⊆ U)
    (hd₁ : ∀ i ∈ P, d ≤ (N₁ i).card) (hd₂ : ∀ i ∈ P, d ≤ (N₂ i).card) :
    ∃ (S : Finset V) (Q : Finset D), S ⊆ U ∧ S.card ≤ 2 * (2 * U.card / d + 1) ∧
      Q ⊆ P ∧ P.card ≤ 4 * Q.card ∧
      ∀ i ∈ Q, (∃ v ∈ S, v ∈ N₁ i) ∧ (∃ v ∈ S, v ∈ N₂ i) := by
  obtain ⟨S₁, Q₁, hS₁U, hS₁c, hQ₁P, hhalf₁, hhit₁⟩ :=
    exists_half_hitting_set U hU P N₁ d hd0 hN₁ hd₁
  obtain ⟨S₂, Q, hS₂U, hS₂c, hQQ₁, hhalf₂, hhit₂⟩ :=
    exists_half_hitting_set U hU Q₁ N₂ d hd0
      (fun i hi => hN₂ i (hQ₁P hi)) (fun i hi => hd₂ i (hQ₁P hi))
  refine ⟨S₁ ∪ S₂, Q, union_subset hS₁U hS₂U, ?_, hQQ₁.trans hQ₁P, by omega, ?_⟩
  · have hc := card_union_le S₁ S₂
    omega
  · intro i hi
    obtain ⟨v, hv, hvi⟩ := hhit₁ i (hQQ₁ hi)
    obtain ⟨w, hw, hwi⟩ := hhit₂ i hi
    exact ⟨⟨v, mem_union_left _ hv, hvi⟩, ⟨w, mem_union_right _ hw, hwi⟩⟩

end SlackSparsification
