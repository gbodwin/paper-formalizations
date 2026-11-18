import OnlineReachabilityPreservers.KnownBudget

/-! Algorithms 4–5 and Theorem 16. Arrivals are indexed from zero. -/

namespace OnlineReachabilityPreservers

open Finset

def dyadicQuota (base level : ℕ) : ℕ := base * 2 ^ level

private def coveringLevels (base index : ℕ) : Finset ℕ :=
  (range (index + 1)).filter (fun k => index + 1 ≤ dyadicQuota base k)

/-- The first dyadic budget that covers this index. -/
def indexLevel (base index : ℕ) : ℕ := (least? (coveringLevels base index)).getD index

private theorem index_in_coveringLevels {base : ℕ} (hbase : 0 < base) (i : ℕ) :
    i ∈ coveringLevels base i := by
  have hp : i + 1 ≤ 2 ^ i := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ]
      omega
  refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_self _), hp.trans ?_⟩
  simpa [dyadicQuota] using Nat.mul_le_mul_right (2 ^ i) (show 1 ≤ base by omega)

theorem indexLevel_covers {base : ℕ} (hbase : 0 < base) (i : ℕ) :
    i + 1 ≤ dyadicQuota base (indexLevel base i) := by
  obtain ⟨k, hk⟩ := least?_some ⟨i, index_in_coveringLevels hbase i⟩
  simpa [indexLevel, hk] using (mem_filter.mp (least?_mem hk)).2

theorem indexLevel_mono {base : ℕ} (hbase : 0 < base) : Monotone (indexLevel base) := by
  intro i j hij
  obtain ⟨k, hk⟩ := least?_some ⟨i, index_in_coveringLevels hbase i⟩
  obtain ⟨l, hl⟩ := least?_some ⟨j, index_in_coveringLevels hbase j⟩
  have hk' := least?_le hk (index_in_coveringLevels hbase i)
  have h : k ≤ l := by
    by_cases hli : l ≤ i
    · apply least?_le hk
      refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hli), ?_⟩
      exact (Nat.succ_le_succ hij).trans (mem_filter.mp (least?_mem hl)).2
    · omega
  simpa [indexLevel, hk, hl] using h

variable {V : Type*} [LinearOrder V]

/-- The assigned path depends on the graph rule, allowed pairs, and the current
arrival index. Each level uses the known-budget assignment for its own quota. -/
def indexSensitivePath (choose : PathRule V) (Q : Finset (V × V))
    (base : ℕ) (F : ℕ → ℕ) (i : ℕ) (d : V × V) : Option (List (V × V)) :=
  let q := dyadicQuota base (indexLevel base i)
  knownBudgetPath choose Q q (F q) d

theorem indexSensitivePath_valid (choose : PathRule V) (G : Arcs V)
    (Q : Finset (V × V)) (base : ℕ) (F : ℕ → ℕ) (i : ℕ) (d : V × V) (hd : d ∈ Q)
    (valid : ∀ A ⊆ G, ∀ q ∈ Q, pathArcs (choose A q) ⊆ G ∧
      (∀ path, choose A q = some path → Walk G q.1 q.2 path) ∧
      (Reach G q.1 q.2 → ∃ path, choose A q = some path)) :
    (∀ path, indexSensitivePath choose Q base F i d = some path → Walk G d.1 d.2 path) ∧
      (Reach G d.1 d.2 → ∃ path, indexSensitivePath choose Q base F i d = some path) :=
  knownBudgetPath_valid choose G Q _ _ d hd valid

def indexSensitiveOutput (choose : PathRule V) (Q : Finset (V × V))
    (base : ℕ) (F : ℕ → ℕ) (D : List (V × V)) : Arcs V :=
  (univ : Finset (Fin D.length)).biUnion fun i =>
    pathArcs (indexSensitivePath choose Q base F i (D.get i))

/-- Finite bound before the two growth inequalities in Theorem 16, footnote 4. -/
theorem indexSensitive_sum_bound (choose : PathRule V) (Q : Finset (V × V))
    (base : ℕ) (F : ℕ → ℕ) (hbase : 0 < base)
    (budget : ∀ (q : ℕ) (T : List (V × V)), T.Nodup → (∀ d ∈ T, d ∈ Q) →
      T.length ≤ q → (runRule choose ∅ T).card ≤ F q)
    (D : List (V × V)) (sub : ∀ d ∈ D, d ∈ Q) :
    (indexSensitiveOutput choose Q base F D).card ≤
      ∑ k ∈ range (indexLevel base (D.length - 1) + 1), 2 * F (dyadicQuota base k) := by
  let levels := range (indexLevel base (D.length - 1) + 1)
  let atLevel (k : ℕ) : Finset (Fin D.length) :=
    univ.filter (fun i => indexLevel base i.1 = k)
  let requests (k : ℕ) : Finset (V × V) := (atLevel k).image D.get
  let planned (k : ℕ) : Arcs V :=
    (requests k).biUnion (fun d => pathArcs (knownBudgetPath choose Q (dyadicQuota base k)
      (F (dyadicQuota base k)) d))
  have hlevels : indexSensitiveOutput choose Q base F D ⊆ levels.biUnion planned := by
    intro e he
    obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
    let k := indexLevel base i.1
    have hk : k ∈ levels :=
      mem_range.mpr (Nat.lt_succ_of_le (indexLevel_mono hbase (by have := i.isLt; omega)))
    have hd : D.get i ∈ requests k :=
      mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩
    exact mem_biUnion.mpr ⟨k, hk, mem_biUnion.mpr ⟨D.get i, hd, hei⟩⟩
  have hlevel (k : ℕ) : (planned k).card ≤ 2 * F (dyadicQuota base k) := by
    have hsub : requests k ⊆ Q := by
      intro d hd
      obtain ⟨i, _, rfl⟩ := mem_image.mp hd
      exact sub _ (List.get_mem D i)
    have hnum : (requests k).card ≤ dyadicQuota base k := by
      apply card_image_le.trans
      let quota := range (dyadicQuota base k)
      have hinj : Set.InjOn (fun (i : Fin D.length) => i.1) (atLevel k) :=
        fun _ _ _ _ h => Fin.ext h
      have hs : (atLevel k).image Fin.val ⊆ quota := by
        intro n hn
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
        have hl : indexLevel base i.1 = k := (mem_filter.mp hi).2
        have hc := indexLevel_covers hbase i.1
        rw [hl] at hc
        exact mem_range.mpr (by omega)
      rw [← card_image_of_injOn hinj, ← card_range (dyadicQuota base k)]
      exact card_le_card hs
    exact theorem15_known_budget choose Q (dyadicQuota base k) (F (dyadicQuota base k))
      (by unfold dyadicQuota; positivity) (budget _) _ hsub hnum
  exact (card_le_card hlevels).trans (card_biUnion_le.trans (sum_le_sum (fun k _ => hlevel k)))

/-- Theorem 16 under the geometric-sum and final-budget comparisons stated
in the paper's footnote. The assignment itself has no final-length input. -/
theorem theorem16_index_sensitive (choose : PathRule V) (Q : Finset (V × V))
    (base : ℕ) (F : ℕ → ℕ) (hbase : 0 < base)
    (budget : ∀ (q : ℕ) (T : List (V × V)), T.Nodup → (∀ d ∈ T, d ∈ Q) →
      T.length ≤ q → (runRule choose ∅ T).card ≤ F q)
    (C₁ C₂ : ℕ)
    (sumBound : ∀ k, (∑ j ∈ range (k + 1), F (dyadicQuota base j)) ≤ C₁ * F (dyadicQuota base k))
    (lastBound : ∀ p, 0 < p → F (dyadicQuota base (indexLevel base (p - 1))) ≤ C₂ * F p)
    (D : List (V × V)) (sub : ∀ d ∈ D, d ∈ Q) :
    (indexSensitiveOutput choose Q base F D).card ≤ 2 * C₁ * C₂ * F D.length := by
  cases D with
  | nil => simp [indexSensitiveOutput]
  | cons d ds =>
    apply (indexSensitive_sum_bound choose Q base F hbase budget (d :: ds) sub).trans
    rw [← mul_sum]
    calc
      _ ≤ 2 * (C₁ * F (dyadicQuota base (indexLevel base ((d :: ds).length - 1)))) :=
        Nat.mul_le_mul_left _ (sumBound _)
      _ ≤ 2 * (C₁ * (C₂ * F ((d :: ds).length))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (lastBound _ (by simp)))
      _ = _ := by ac_rfl

end OnlineReachabilityPreservers
