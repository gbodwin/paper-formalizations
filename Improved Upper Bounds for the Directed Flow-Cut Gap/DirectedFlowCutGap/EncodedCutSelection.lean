import DirectedFlowCutGap.FractionalCoverRawCore
import DirectedFlowCutGap.EncodedUniformRounding
import Mathlib.Data.Fintype.Option

/-!
# Minimum of a list of sampled cuts

The cost comparison uses the stored rational costs. One execution of each
draw tree supplies a candidate, and the selected mask is one of those actual
outputs. Its expected cost is bounded by that of each candidate program.
-/

namespace DirectedFlowCutGap.EncodedCutSelection

open scoped NNReal
open FiniteDrawTrees FiniteAmplification RetainedGridState
open FractionalCoverRawCore RawNonnegativeRational EncodedUnitCostReplication

attribute [local instance] EncodedUniformRounding.flagsFintype

def maskCost {n : ℕ} (costs : RawRow n) (mask : Flags n) : Code :=
  sumCodes (List.ofFn fun i => if mask[i.val] then get costs i else Code.zero)

theorem maskCost_value {n : ℕ} (costs : RawRow n) (mask : Flags n) :
    (maskCost costs mask).realValue = cutCost (fun i => (get costs i).realValue) (selectedSet mask) := by
  have hsum (xs : List Code) : (sumCodes xs).realValue = (xs.map Code.realValue).sum := by
    induction xs with
    | nil => simp [sumCodes, Code.realValue]
    | cons q qs ih => simp [sumCodes, Code.realValue, ← ih]
  rw [maskCost, hsum, List.map_ofFn, List.sum_ofFn, cutCost, selectedSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hm : mask[i.val] <;> simp [hm, Code.realValue]

def cheaper {n : ℕ} (costs : RawRow n) (a b : Flags n) : Flags n :=
  if (maskCost costs a).le (maskCost costs b) then a else b

theorem cheaper_mem {n : ℕ} (costs : RawRow n) (a b : Flags n) :
    cheaper costs a b = a ∨ cheaper costs a b = b := by
  unfold cheaper
  split_ifs <;> simp

noncomputable def cutPrice {n : ℕ} (costs : RawRow n) (a : Flags n) : ℝ :=
  cutCost (fun i => (get costs i).realValue) (selectedSet a)

theorem cutPrice_cheaper {n : ℕ} (costs : RawRow n) (a b : Flags n) :
    cutPrice costs (cheaper costs a b) ≤ cutPrice costs a ∧
      cutPrice costs (cheaper costs a b) ≤ cutPrice costs b := by
  unfold cheaper
  split_ifs with h
  · refine ⟨le_rfl, ?_⟩
    have hle := (Code.le_eq_true _ _).mp h
    unfold cutPrice
    rw [← maskCost_value, ← maskCost_value]
    simpa only [Code.realValue, NNReal.coe_le_coe, NNRat.cast_le] using hle
  · refine ⟨?_, le_rfl⟩
    have hle := le_of_not_ge (fun hh => h ((Code.le_eq_true _ _).mpr hh))
    unfold cutPrice
    rw [← maskCost_value, ← maskCost_value]
    simpa only [Code.realValue, NNReal.coe_le_coe, NNRat.cast_le] using hle

def best {n : ℕ} (costs : RawRow n) : List (FiniteDrawTrees.Tree (Flags n)) →
    FiniteDrawTrees.Tree (Option (Flags n))
  | [] => .pure none
  | t :: ts => FiniteDrawTrees.bind t fun a =>
      map (fun b => some (b.elim a (cheaper costs a))) (best costs ts)

theorem best_none_iff {n : ℕ} (costs : RawRow n) (ts : List (FiniteDrawTrees.Tree (Flags n))) :
    none ∈ (ideal (best costs ts)).support ↔ ts = [] := by
  cases ts with
  | nil => simp [best, ideal, law]
  | cons t ts =>
    simp only [best, ideal, law_bind, law_map, List.cons_ne_nil, iff_false]
    intro hn
    obtain ⟨a, _, ha⟩ := (PMF.mem_support_bind_iff _ _ _).mp hn
    obtain ⟨b, _, hb⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
    cases b <;> simp at hb

theorem best_support {n : ℕ} (costs : RawRow n) (ts : List (FiniteDrawTrees.Tree (Flags n)))
    {mask : Flags n} (h : some mask ∈ (ideal (best costs ts)).support) :
    ∃ t ∈ ts, mask ∈ (ideal t).support := by
  induction ts generalizing mask with
  | nil => simp [best, ideal, law] at h
  | cons t ts ih =>
    simp only [best, ideal, law_bind, law_map] at h
    obtain ⟨a, ha, hh⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    obtain ⟨b, hb, hmask⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
    cases b with
    | none =>
      have he : a = mask := Option.some.inj hmask
      exact ⟨t, List.mem_cons_self, he ▸ ha⟩
    | some b =>
      have he : cheaper costs a b = mask := Option.some.inj hmask
      rcases cheaper_mem costs a b with h | h
      · exact ⟨t, List.mem_cons_self, (h.symm.trans he) ▸ ha⟩
      · obtain ⟨u, hu, hv⟩ := ih hb
        exact ⟨u, List.mem_cons_of_mem _ hu, (h.symm.trans he) ▸ hv⟩

theorem best_within {n : ℕ} (costs : RawRow n) (ts : List (FiniteDrawTrees.Tree (Flags n)))
    (B : ℕ) (h : ∀ t ∈ ts, Within B t) : Within (ts.length * B) (best costs ts) := by
  induction ts with
  | nil => exact .pure _ _
  | cons t ts ih =>
    simp only [best, List.length_cons, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_comm]
    apply within_bind (h t List.mem_cons_self)
    intro a
    exact within_map (ih (fun u hu => h u (List.mem_cons_of_mem _ hu))) _

noncomputable def optionPrice {n : ℕ} (costs : RawRow n) : Option (Flags n) → ℝ :=
  fun x => x.elim 0 (cutPrice costs)

theorem best_widths {n w : ℕ} (costs : RawRow n) (ts : List (FiniteDrawTrees.Tree (Flags n)))
    (h : ∀ t ∈ ts, LazyFairBitTrees.WidthsLE w t) : LazyFairBitTrees.WidthsLE w (best costs ts) := by
  induction ts with
  | nil => exact .pure _
  | cons t ts ih =>
    unfold best
    apply LazyFairBitTrees.widths_bind (h t (List.mem_cons_self ..))
    intro a
    exact LazyFairBitTrees.widths_map (ih (fun u hu => h u (List.mem_cons_of_mem t hu))) _

private theorem expected_map_le {A B : Type} [Fintype A] [Fintype B] (p : PMF A)
    (f : A → B) (c : B → ℝ) (g : A → ℝ) (h : ∀ a ∈ p.support, c (f a) ≤ g a) :
    expectedCost (p.map f) c ≤ expectedCost p g := by
  rw [expectedCost_map]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_ne_iff] using ha
    simp [hz]

theorem expected_best_le {n : ℕ} (costs : RawRow n)
    (ts : List (FiniteDrawTrees.Tree (Flags n))) {t : FiniteDrawTrees.Tree (Flags n)} (ht : t ∈ ts) :
    expectedCost (ideal (best costs ts)) (optionPrice costs) ≤
      expectedCost (ideal t) (cutPrice costs) := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
    let p := ideal u
    let q := ideal (best costs us)
    let select := fun (a : Flags n) (b : Option (Flags n)) => some (b.elim a (cheaper costs a))
    simp only [best, ideal, law_bind, law_map, expectedCost_bind]
    change (∑ a, (p a).toReal * expectedCost (q.map (select a)) (optionPrice costs)) ≤ _
    rcases List.mem_cons.mp ht with rfl | ht
    · apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have hcost : ∀ b ∈ q.support, optionPrice costs (select a b) ≤ cutPrice costs a := by
        intro b _
        cases b with
        | none => exact le_rfl
        | some b => exact (cutPrice_cheaper costs a b).1
      exact (expected_map_le q (select a) (optionPrice costs) (fun _ => cutPrice costs a) hcost).trans_eq
        (by simp only [expectedCost, ← Finset.sum_mul, sum_probability_toReal, one_mul])
    · apply le_trans _ (ih ht)
      calc
        _ ≤ ∑ a, (p a).toReal * expectedCost q (optionPrice costs) := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          apply expected_map_le
          intro b hb
          cases b with
          | none =>
            have he := (best_none_iff costs us).mp hb
            simp [he] at ht
          | some b => exact (cutPrice_cheaper costs a b).2
        _ = _ := by rw [← Finset.sum_mul, sum_probability_toReal, one_mul]

end DirectedFlowCutGap.EncodedCutSelection
