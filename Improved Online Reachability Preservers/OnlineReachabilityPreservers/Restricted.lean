import Mathlib.Analysis.Real.Sqrt
import OnlineReachabilityPreservers.Online

/-! Theorem 11, by counting collisions between new-edge tails. -/

namespace OnlineReachabilityPreservers

open Finset

section Counting

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- Path indices at which a vertex is marked. -/
def occurrences (marks : I → Finset V) (v : V) : Finset I :=
  univ.filter (fun i => v ∈ marks i)

/-- A marked vertex and two distinct path indices in increasing order. -/
def collisions (marks : I → Finset V) : Finset (V × I × I) :=
  univ.filter (fun x => x.2.1 < x.2.2 ∧ x.1 ∈ marks x.2.1 ∧ x.1 ∈ marks x.2.2)

omit [LinearOrder I] in
theorem sum_occurrences (marks : I → Finset V) :
    (∑ v, (occurrences marks v).card) = ∑ i, (marks i).card := by
  simp only [occurrences, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  congr 1
  ext
  simp

private theorem collision_count (marks : I → Finset V) :
    (collisions marks).card = ∑ v, (occurrences marks v).card.choose 2 := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (by simp)]
  apply sum_congr rfl
  intro v _
  let s := occurrences marks v
  let embed : I × I ↪ V × I × I := ⟨fun p => (v, p), fun _ _ h => congrArg Prod.snd h⟩
  have fiber : ((collisions marks).filter fun x => x.1 = v) =
      ((s ×ˢ s).filter (fun p => p.1 < p.2)).map embed := by
    ext ⟨w, i, j⟩
    constructor
    · intro h
      obtain ⟨hm, rfl⟩ := mem_filter.mp h
      have ⟨hlt, hi, hj⟩ : i < j ∧ w ∈ marks i ∧ w ∈ marks j :=
        (mem_filter.mp hm).2
      have his : i ∈ s := mem_filter.mpr ⟨mem_univ _, hi⟩
      have hjs : j ∈ s := mem_filter.mpr ⟨mem_univ _, hj⟩
      exact mem_map.mpr ⟨(i, j), mem_filter.mpr ⟨mem_product.mpr ⟨his, hjs⟩, hlt⟩, rfl⟩
    · intro h
      obtain ⟨⟨i', j'⟩, hp, he⟩ := mem_map.mp h
      change (v, i', j') = (w, i, j) at he
      cases he
      obtain ⟨hp, hlt⟩ := mem_filter.mp hp
      obtain ⟨hi, hj⟩ := mem_product.mp hp
      exact mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_univ _, hlt, (mem_filter.mp hi).2, (mem_filter.mp hj).2⟩, rfl⟩
  rw [fiber, card_map, card_product_filter_lt]

private theorem square_choose (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
  rw [Nat.choose_two_right, mul_comm 2, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  cases n with
  | zero => simp
  | succ k => simp [pow_two, Nat.mul_succ, Nat.add_comm]

/-- Finite double counting of repeated incidences and Cauchy–Schwarz. -/
theorem incidence_square (marks : I → Finset V) (B : ℕ)
    (bound : (collisions marks).card ≤ B) :
    (∑ i, (marks i).card) ^ 2 ≤ Fintype.card V * ((∑ i, (marks i).card) + 2 * B) := by
  rw [← sum_occurrences]
  have hCS := sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset V)
    (fun _ => 1) (fun v => (occurrences marks v).card)
  rw [collision_count] at bound
  calc
    _ ≤ Fintype.card V * ∑ v, (occurrences marks v).card ^ 2 := by
      simpa using hCS
    _ = Fintype.card V * ((∑ v, (occurrences marks v).card) +
        2 * ∑ v, (occurrences marks v).card.choose 2) := by
      simp only [square_choose, sum_add_distrib, mul_sum]
    _ ≤ _ := by gcongr

end Counting

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Two collisions with the same earlier round and later sink are identical. -/
private theorem one_collision {G : Arcs V} {D : List (V × V)} {i j k : Fin D.length}
    (hij : i < j) (hik : i < k) {x y : V}
    (xi : x ∈ marks G D i) (xj : x ∈ marks G D j)
    (yi : y ∈ marks G D i) (yk : y ∈ marks G D k)
    (ht : (D.get j).2 = (D.get k).2) : x = y ∧ j = k := by
  obtain ⟨a, ha, hax⟩ := mem_image.mp xi
  obtain ⟨b, hb, hbx⟩ := mem_image.mp xj
  obtain ⟨c, hc, hcy⟩ := mem_image.mp yi
  obtain ⟨d, hd, hdy⟩ := mem_image.mp yk
  have hxy : x = y := by
    by_contra hne
    have hac : a ≠ c := by
      intro h
      exact hne (hax.symm.trans ((congrArg Prod.fst h).trans hcy))
    rcases forward_edge_order (before_subset G D i) (mem_sdiff.mp ha).1
        (mem_sdiff.mp hc).1 hac with h | h
    · apply earlier_edge_conflict hij ha hb (hax.trans hbx.symm)
      have edge : Edge G d.1 d.2 :=
        forwardEdges_subset (before_subset G D k) _ (mem_sdiff.mp hd).1
      have hr : Reach G c.1 (D.get k).2 :=
        (hcy.trans hdy.symm) ▸ (new_edge_reaches_target hd).head edge
      exact ht.symm ▸ h.trans hr
    · apply earlier_edge_conflict hik hc hd (hcy.trans hdy.symm)
      have edge : Edge G b.1 b.2 :=
        forwardEdges_subset (before_subset G D j) _ (mem_sdiff.mp hb).1
      have hr : Reach G a.1 (D.get j).2 :=
        (hax.trans hbx.symm) ▸ (new_edge_reaches_target hb).head edge
      exact ht ▸ h.trans hr
  refine ⟨hxy, ?_⟩
  have hbd : b.1 = d.1 := hbx.trans (hxy.trans hdy.symm)
  rcases lt_trichotomy j k with hjk | hjk | hkj
  · exact (earlier_edge_conflict hjk hb hd hbd (ht ▸ new_edge_reaches_target hb)).elim
  · exact hjk
  · exact (earlier_edge_conflict hkj hd hb hbd.symm (ht.symm ▸ new_edge_reaches_target hd)).elim

private theorem bound_collisions (G : Arcs V) (D : List (V × V)) (S : Finset V)
    (sinks : ∀ d ∈ D, d.2 ∈ S) :
    (collisions (marks G D)).card ≤ D.length * S.card := by
  let charge : V × Fin D.length × Fin D.length → Fin D.length × V :=
    fun x => (x.2.1, (D.get x.2.2).2)
  have injective : Set.InjOn charge (collisions (marks G D)) := by
    intro a ha b hb heq
    rcases a with ⟨x, i, j⟩
    rcases b with ⟨y, i', k⟩
    change (i, (D.get j).2) = (i', (D.get k).2) at heq
    obtain ⟨hi, ht⟩ := Prod.mk.inj heq
    subst i'
    have hm : (x, i, j) ∈ collisions (marks G D) := ha
    have hn : (y, i, k) ∈ collisions (marks G D) := hb
    obtain ⟨_, hij, xi, xj⟩ := mem_filter.mp hm
    obtain ⟨_, hik, yi, yk⟩ := mem_filter.mp hn
    obtain ⟨rfl, rfl⟩ := one_collision hij hik xi xj yi yk ht
    rfl
  calc
    _ = ((collisions (marks G D)).image charge).card := (card_image_of_injOn injective).symm
    _ ≤ ((univ : Finset (Fin D.length)) ×ˢ S).card := by
      apply card_le_card
      intro q hq
      obtain ⟨⟨v, i, j⟩, _, rfl⟩ := mem_image.mp hq
      exact mem_product.mpr ⟨mem_univ _, sinks _ (List.get_mem D j)⟩
    _ = _ := by simp

/-- Exact finite sink-restricted bound on the actual output of Algorithm 1. -/
theorem forwardRun_card_square {G : Arcs V} (dag : IsDAG G)
    (D : List (V × V)) (S : Finset V) (sinks : ∀ d ∈ D, d.2 ∈ S) :
    (forwardRun G D).card ^ 2 ≤
      Fintype.card V * ((forwardRun G D).card + 2 * (D.length * S.card)) := by
  have h := incidence_square (marks G D) (D.length * S.card) (bound_collisions G D S sinks)
  rwa [sum_marks_card dag] at h

private theorem sqrt_budget {n m q : ℕ} (h : m ^ 2 ≤ n * (m + 2 * q)) :
    (m : ℝ) ≤ n + Real.sqrt (2 * n * q) := by
  have hs : (m : ℝ) ^ 2 ≤ n * ((m : ℝ) + 2 * q) := by exact_mod_cast h
  by_contra! hn
  have h0 := Real.sqrt_nonneg (2 * (n : ℝ) * q)
  have hn' : 0 < (m : ℝ) - n := by linarith
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * n * q by positivity)
  have hprod := mul_nonneg (show (0 : ℝ) ≤ n by positivity) (le_of_lt hn')
  have hgap := mul_pos
    (show 0 < (m : ℝ) - n - Real.sqrt (2 * n * q) by linarith)
    (show 0 < (m : ℝ) - n + Real.sqrt (2 * n * q) by linarith)
  nlinarith only [hs, hsq, hprod, hgap]

/-- The DAG sink case of Theorem 11. The algorithm receives only the graph and the trace. -/
theorem theorem11_sinks {G : Arcs V} (dag : IsDAG G)
    (D : List (V × V)) (S : Finset V) (sinks : ∀ d ∈ D, d.2 ∈ S) :
    Preserves G (forwardRun G D) D ∧
      ((forwardRun G D).card : ℝ) ≤
        Fintype.card V + Real.sqrt (2 * Fintype.card V * D.length * S.card) := by
  refine ⟨forwardRun_preserves dag D, ?_⟩
  simpa [Nat.cast_mul, mul_assoc] using sqrt_budget (forwardRun_card_square dag D S sinks)

/-- Run Algorithm 2 by maintaining the preserver with orientation reversed. -/
def backwardRun (G : Arcs V) (D : List (V × V)) : Arcs V :=
  reverseArcs (forwardRun (reverseArcs G) (D.map Prod.swap))

theorem backwardRun_prefix (G : Arcs V) {D D' : List (V × V)} (h : D <+: D') :
    backwardRun G D ⊆ backwardRun G D' :=
  reverseArcs_mono (forwardRun_prefix _ (h.map _))

/-- The DAG source case of Theorem 11. -/
theorem theorem11_sources {G : Arcs V} (dag : IsDAG G)
    (D : List (V × V)) (S : Finset V) (sources : ∀ d ∈ D, d.1 ∈ S) :
    Preserves G (backwardRun G D) D ∧
      ((backwardRun G D).card : ℝ) ≤
        Fintype.card V + Real.sqrt (2 * Fintype.card V * D.length * S.card) := by
  obtain ⟨preserves, budget⟩ := theorem11_sinks (reverseArcs_dag dag) (D.map Prod.swap) S (by
    intro d hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
    exact sources q hq)
  refine ⟨?_, by simpa [backwardRun] using budget⟩
  intro d hd
  have h := preserves d.swap (List.mem_map.mpr ⟨d, hd, rfl⟩)
  rw [backwardRun, reach_reverseArcs]
  exact h.trans reach_reverseArcs

end OnlineReachabilityPreservers
