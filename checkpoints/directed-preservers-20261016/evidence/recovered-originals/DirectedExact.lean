import SlackSparsification.DirectedTrees
import SlackSparsification.Hitting
import SlackSparsification.PlusFourParameters
import Mathlib.Tactic

/-! Theorems 3–4: actual directed weighted preservers with slack.
Shortest paths, hitting sets and in/out trees are constructed internally. -/
namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped ENNReal NNReal BigOperators
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

theorem exists_exact_slack_paths (K : SimpleGraph V) (A : V → V → Prop) (w : V → V → ℝ≥0)
    (src dst : D → V) (p : ∀ i, K.Walk (src i) (dst i)) (hp : ∀ i, Optimal A w (p i))
    (P : Finset D) (l : ℕ) :
    ∃ (F : Finset (V × V)) (Q : Finset D), (∀ e ∈ F, A e.1 e.2) ∧ Q ⊆ P ∧
      P.card ≤ 2 * Q.card ∧ F.card ≤ P.card * l + 2 * Fintype.card V * (2 * Fintype.card V / (l + 1) + 1) ∧
      ∀ i ∈ Q, distance K (edgeRel F) w (src i) (dst i) = distance K A w (src i) (dst i) := by
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
        List.toFinset_card_of_nodup (hp i).2.1.support_nodup, Walk.length_support]
    omega
  obtain ⟨S, Q₁, _, hSc, hQ₁L, hhalf, hhit⟩ := exists_half_hitting_set
    (univ : Finset V) univ_nonempty L N (l + 1) (by omega)
    (by intro i _; exact subset_univ _) hN
  choose T hTc hTA hTd using fun r : V => exists_root_preserver K A w r
  let F := B.biUnion (fun i => arcs (p i)) ∪ S.biUnion T
  have hFA : ∀ e ∈ F, A e.1 e.2 := by
    intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
      exact arcs_allowed (p i) (hp i).1 hi
    · obtain ⟨r, _, hr⟩ := mem_biUnion.mp he
      exact hTA r e hr
  have hFc : F.card ≤ P.card * l + 2 * Fintype.card V * (2 * Fintype.card V / (l + 1) + 1) := by
    have hBc : (B.biUnion fun i => arcs (p i)).card ≤ P.card * l := calc
      _ ≤ ∑ i ∈ B, (arcs (p i)).card := card_biUnion_le
      _ ≤ ∑ _ ∈ B, l := sum_le_sum (fun i hi => (arcs_card_le (p i)).trans (mem_filter.mp hi).2)
      _ = B.card * l := by simp
      _ ≤ P.card * l := Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
    have hTc' : (S.biUnion T).card ≤ 2 * Fintype.card V * (2 * Fintype.card V / (l + 1) + 1) := calc
      _ ≤ ∑ r ∈ S, (T r).card := card_biUnion_le
      _ ≤ ∑ _ ∈ S, 2 * Fintype.card V := sum_le_sum (fun r _ => hTc r)
      _ = S.card * (2 * Fintype.card V) := by simp
      _ ≤ _ := by simpa [Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_right (2 * Fintype.card V) hSc
    exact (card_union_le _ _).trans (Nat.add_le_add hBc hTc')
  let Q := B ∪ Q₁
  have hBP : B ⊆ P := filter_subset _ _
  have hdis : Disjoint B Q₁ := disjoint_left.mpr (by
    intro i hi hi₁
    exact (mem_sdiff.mp (hQ₁L hi₁)).2 hi)
  refine ⟨F, Q, hFA, union_subset hBP (hQ₁L.trans sdiff_subset), ?_, hFc, ?_⟩
  · have hc := card_sdiff_add_card_eq_card hBP
    have hq := card_union_of_disjoint hdis
    change L.card + B.card = P.card at hc
    change P.card ≤ 2 * (B ∪ Q₁).card
    omega
  · intro i hi
    apply le_antisymm _ (distance_mono w (fun u v h => hFA (u,v) h) _ _)
    rcases mem_union.mp hi with hi | hi
    · rw [distance_eq_cost (hp i)]
      apply distance_le_cost w (p i)
      apply allowed_of_arcs
      intro e he
      exact mem_union_left _ (mem_biUnion.mpr ⟨i, hi, he⟩)
    · obtain ⟨r, hrS, hrN⟩ := hhit i hi
      have hTsub : ∀ u v, edgeRel (T r) u v → edgeRel F u v := by
        intro u v h
        exact mem_union_right _ (mem_biUnion.mpr ⟨r, hrS, h⟩)
      calc
        _ ≤ distance K (edgeRel F) w (src i) r + distance K (edgeRel F) w r (dst i) := distance_triangle _ _ _ _ _
        _ ≤ distance K (edgeRel (T r)) w (src i) r + distance K (edgeRel (T r)) w r (dst i) :=
          add_le_add (distance_mono w hTsub _ _) (distance_mono w hTsub _ _)
        _ = distance K A w (src i) r + distance K A w r (dst i) := by rw [(hTd r (src i)).2, (hTd r (dst i)).1]
        _ = _ := distance_split (p i) (hp i) r (List.mem_toFinset.mp hrN)

theorem exact_integer_budget (n p k : ℕ) (hk : 0 < k) (hp : p ≤ k ^ 2) :
    p * (n / k) + 2 * n * (2 * n / (n / k + 1) + 1) ≤ 7 * n * k := by
  let l := n / k
  have hl : l * k ≤ n := Nat.div_mul_le_self _ _
  have hl' : n < 1 * (l + 1) * k := by simpa [l, Nat.mul_comm] using Nat.lt_mul_div_succ n hk
  have hr := root_quotient_bound n 1 l k (by omega) hl'
  simp only [one_mul] at hr
  have hshort : p * l ≤ n * k := by
    have ha := Nat.mul_le_mul_right l hp
    have hb := Nat.mul_le_mul_right k hl
    nlinarith
  change p * l + 2 * n * (2 * n / (l + 1) + 1) ≤ _
  have hb := Nat.mul_le_mul_left (2 * n) hr
  have hn := Nat.mul_le_mul_left n (show 1 ≤ k by omega)
  nlinarith

end SlackSparsification.Directed
