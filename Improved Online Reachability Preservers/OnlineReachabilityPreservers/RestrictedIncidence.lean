import OnlineReachabilityPreservers.Bridges

/-! The reverse-arrival selection and dense sink-restricted incidence estimate. -/

namespace OnlineReachabilityPreservers

open Finset

section Selection

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- The degree of a vertex just after inserting the given path in reverse order. -/
def reverseArrivalDegree (paths : I → Finset V) (i : I) (v : V) : ℕ :=
  ((occurrences paths v).filter (i ≤ ·)).card

/-- Lemma 12. At some insertion, at least a quarter of the average path length
consists of vertices with at least a quarter of the final average degree. -/
theorem lemma12_reverse_arrival (paths : I → Finset V)
    (massPos : 0 < ∑ i, (paths i).card) :
    ∃ i, (∑ j, (paths j).card) ≤ 4 * Fintype.card I *
      ((paths i).filter (fun v => (∑ j, (paths j).card) ≤
        4 * Fintype.card V * reverseArrivalDegree paths i v)).card := by
  let M := ∑ i, (paths i).card
  let high (i : I) (v : V) := M ≤ 4 * Fintype.card V * reverseArrivalDegree paths i v
  let lowIndices (v : V) := (occurrences paths v).filter fun i => ¬ high i v
  change ∃ i, M ≤ 4 * Fintype.card I * ((paths i).filter (high i)).card
  by_contra! smallPaths
  have fewLow (v : V) : 4 * Fintype.card V * (lowIndices v).card ≤ M := by
    by_cases nonempty : (lowIndices v).Nonempty
    · let i := (lowIndices v).min' nonempty
      have hit : i ∈ lowIndices v := min'_mem _ _
      have low : ¬ high i v := (mem_filter.mp hit).2
      have subset : lowIndices v ⊆ (occurrences paths v).filter (i ≤ ·) :=
        fun j mem => mem_filter.mpr ⟨(mem_filter.mp mem).1, min'_le _ _ mem⟩
      exact (Nat.mul_le_mul_left _ (card_le_card subset)).trans (le_of_lt (lt_of_not_ge low))
    · simp [not_nonempty_iff_eq_empty.mp nonempty]
  have lowMass : ∑ i, ((paths i).filter (fun v => ¬ high i v)).card =
      ∑ v, (lowIndices v).card := by
    let lowPaths (i : I) := (paths i).filter (fun v => ¬ high i v)
    have eq (v : V) : occurrences lowPaths v = lowIndices v := by
      ext i
      simp [lowPaths, lowIndices, mem_occurrences]
    change ∑ i, (lowPaths i).card = _
    rw [← sum_occurrences, sum_congr rfl fun v _ => congrArg card (eq v)]
  have total : (∑ i, ((paths i).filter (high i)).card) + (∑ v, (lowIndices v).card) = M := by
    rw [← lowMass, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => card_filter_add_card_filter_not (s := paths i) (high i)
  have hi : 4 * Fintype.card I * (∑ i, ((paths i).filter (high i)).card) ≤ Fintype.card I * M := by
    rw [mul_sum, ← card_univ (α := I)]
    calc
      _ ≤ ∑ _ : I, M := sum_le_sum fun i _ => (smallPaths i).le
      _ = _ := sum_const_nat fun _ _ => rfl
  have lo : 4 * Fintype.card V * (∑ v, (lowIndices v).card) ≤ Fintype.card V * M := by
    rw [mul_sum, ← card_univ (α := V)]
    calc
      _ ≤ ∑ _ : V, M := sum_le_sum fun v _ => fewLow v
      _ = _ := sum_const_nat fun _ _ => rfl
  have mpos : 0 < M := massPos
  have ipos : 0 < Fintype.card I := by
    by_contra! h
    have empty : IsEmpty I := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    exact (Nat.ne_of_gt mpos) (by simp [M])
  have vpos : 0 < Fintype.card V := by
    by_contra! h
    have empty : IsEmpty V := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    exact (Nat.ne_of_gt mpos) (by simp [M, eq_empty_of_isEmpty])
  rw [mul_comm 4 (Fintype.card I), mul_assoc] at hi
  rw [mul_comm 4 (Fintype.card V), mul_assoc] at lo
  have hi' := (Nat.mul_le_mul_left_iff ipos).mp hi
  have lo' := (Nat.mul_le_mul_left_iff vpos).mp lo
  omega

end Selection

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Lemma 13 for the compressed paths of a distinct sink-restricted trace.
The squared mass bound is the inequality on the product of the two averages
with the positive vertex and path counts cleared. -/
theorem lemma13_compressed_mass_square {G : Arcs V} (dag : IsDAG G)
    (D : List (V × V)) (distinct : D.Nodup) (S : Finset V)
    (sinks : ∀ d ∈ D, d.2 ∈ S)
    (dense : 2 * Fintype.card V ≤ ∑ i : Fin D.length, (compressed G D i).card) :
    (∑ i : Fin D.length, (compressed G D i).card) ^ 2 ≤
      24 * Fintype.card V * D.length * S.card := by
  rw [compressed_total dag] at dense ⊢
  let n := Fintype.card V
  let p := D.length
  let m := (forwardRun G D).card
  let s := S.card
  change 2 * n ≤ m + p at dense
  change (m + p) ^ 2 ≤ 24 * n * p * s
  have count : p ≤ n * s := by
    have sub : D.toFinset ⊆ (univ : Finset V) ×ˢ S :=
      fun d hd => mem_product.mpr ⟨mem_univ _, sinks _ (List.mem_toFinset.mp hd)⟩
    have card := card_le_card sub
    simpa [p, n, s, List.toFinset_card_of_nodup distinct, card_product] using card
  have cost : (m : ℝ) ≤ n + Real.sqrt (2 * n * p * s) := by
    simpa [m, n, p, s] using (theorem11_sinks dag D S sinks).2
  have denseReal : 2 * (n : ℝ) ≤ m + p := by exact_mod_cast dense
  have countReal : (p : ℝ) ≤ n * s := by exact_mod_cast count
  let r := Real.sqrt (2 * (n : ℝ) * p * s)
  have rnonneg : 0 ≤ r := Real.sqrt_nonneg _
  have rsq : r ^ 2 = 2 * (n : ℝ) * p * s := Real.sq_sqrt (by positivity)
  have half : (m + (p : ℝ)) ≤ 2 * (r + p) := by
    change (m : ℝ) ≤ n + r at cost
    linarith only [cost, denseReal]
  have masssq : (m + (p : ℝ)) ^ 2 ≤ (2 * (r + p)) ^ 2 := by
    gcongr
  have psq : (p : ℝ) ^ 2 ≤ n * p * s := by
    have multiplied := mul_le_mul_of_nonneg_left countReal (Nat.cast_nonneg p)
    nlinarith only [multiplied]
  have bound : (m + (p : ℝ)) ^ 2 ≤ 24 * (n : ℝ) * p * s := by
    nlinarith only [masssq, rsq, psq, sq_nonneg (r - p)]
  exact_mod_cast bound

end OnlineReachabilityPreservers
