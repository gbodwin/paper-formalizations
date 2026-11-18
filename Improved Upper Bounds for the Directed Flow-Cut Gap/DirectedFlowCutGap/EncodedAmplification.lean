import DirectedFlowCutGap.LazyFairBitTrees
import DirectedFlowCutGap.FairBitConfidence
import DirectedFlowCutGap.RawNonnegativeRational

/-!
# Executable minimum-cost amplification with bounded fair bits

Each executed sample comes from the same retained tree. The minimum is
computed by comparing stored rational prices. The ideal product law and
the accumulated bounded-rejection error are proved for that program.
-/

namespace DirectedFlowCutGap.EncodedAmplification

open scoped NNReal ENNReal
open FiniteDrawTrees FiniteAmplification RawNonnegativeRational

def samples {A : Type} (tree : FiniteDrawTrees.Tree A) :
    (n : ℕ) → FiniteDrawTrees.Tree (Fin n → A)
  | 0 => .pure Fin.elim0
  | n + 1 => FiniteDrawTrees.bind tree fun a => map (Fin.cons a) (samples tree n)

theorem samples_within {A : Type} {tree : FiniteDrawTrees.Tree A} {Q : ℕ}
    (h : Within Q tree) (n : ℕ) : Within (n * Q) (samples tree n) := by
  induction n with
  | zero => exact .pure _ _
  | succ n ih =>
    let next (a : A) : FiniteDrawTrees.Tree (Fin (n + 1) → A) :=
      map (Fin.cons (α := fun _ => A) a) (samples tree n)
    have hh' (a : A) : Within (n * Q) (next a) :=
      within_map ih (Fin.cons (α := fun _ => A) a)
    have hh : Within (Q + n * Q) (FiniteDrawTrees.bind tree next) :=
      within_bind h next hh'
    simpa only [samples, Nat.succ_mul, Nat.add_comm] using
      hh

theorem samples_widths {A : Type} {tree : FiniteDrawTrees.Tree A} {width : ℕ}
    (h : LazyFairBitTrees.WidthsLE width tree) (n : ℕ) :
    LazyFairBitTrees.WidthsLE width (samples tree n) := by
  induction n with
  | zero => exact .pure _
  | succ n ih =>
    let next (a : A) : FiniteDrawTrees.Tree (Fin (n + 1) → A) :=
      map (Fin.cons (α := fun _ => A) a) (samples tree n)
    have hh (a : A) : LazyFairBitTrees.WidthsLE width (next a) :=
      LazyFairBitTrees.widths_map ih (Fin.cons (α := fun _ => A) a)
    exact LazyFairBitTrees.widths_bind h next hh

private theorem cons_map_apply {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (p : PMF (Fin n → A))
    (a : A) (x : Fin (n + 1) → A) :
    (p.map (Fin.cons a)) x = if a = x 0 then p (Fin.tail x) else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  by_cases h : a = x 0
  · subst a
    rw [ite_eq_left rfl, Finset.sum_eq_single (Fin.tail x)]
    · rw [Fin.cons_self_tail, ite_eq_left rfl]
    · intro y _ hy
      apply ite_eq_right
      intro he
      apply hy
      simpa only [Fin.tail_cons] using congrArg Fin.tail he.symm
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro y _
    apply ite_eq_right
    intro he
    apply h
    simpa only [Fin.cons_zero] using congrFun he.symm 0

theorem samples_law {A : Type} [Fintype A] (tree : FiniteDrawTrees.Tree A) (n : ℕ) :
    ideal (samples tree n) = sampleLaw (ideal tree) n := by
  classical
  induction n with
  | zero =>
    ext x
    have hx : x = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [samples, ideal, law, hx, PMF.pure_apply]
  | succ n ih =>
    ext x
    simp only [samples, ideal, law_bind, law_map, ih]
    rw [PMF.bind_apply, tsum_fintype, sampleLaw_apply, Fin.prod_univ_succ]
    simp_rw [cons_map_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [sampleLaw_apply, Fin.tail]

def cheaper {A : Type} (price : A → Code) (a b : A) : A :=
  if (price a).le (price b) then a else b

private theorem cheaper_cases {A : Type} (price : A → Code) (a b : A) :
    cheaper price a b = a ∨ cheaper price a b = b := by
  unfold cheaper
  split_ifs <;> simp

private theorem cheaper_price {A : Type} (price : A → Code) (a b : A) :
    (price (cheaper price a b)).realValue ≤ (price a).realValue ∧
      (price (cheaper price a b)).realValue ≤ (price b).realValue := by
  unfold cheaper
  split_ifs with h
  · exact ⟨le_rfl, by
      have hh := (Code.le_eq_true _ _).mp h
      change ((price a).value : ℝ≥0) ≤ ((price b).value : ℝ≥0)
      exact_mod_cast hh⟩
  · exact ⟨by
      have hh := le_of_not_ge (fun hh => h ((Code.le_eq_true _ _).mpr hh))
      change ((price b).value : ℝ≥0) ≤ ((price a).value : ℝ≥0)
      exact_mod_cast hh, le_rfl⟩

def minimum {A : Type} (price : A → Code) : (n : ℕ) → (Fin (n + 1) → A) → A
  | 0, x => x 0
  | n + 1, x => cheaper price (x 0) (minimum price n (Fin.tail x))

theorem minimum_is_sample {A : Type} (price : A → Code) (n : ℕ) (x : Fin (n + 1) → A) :
    ∃ i, minimum price n x = x i := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rcases cheaper_cases price (x 0) (minimum price n (Fin.tail x)) with h | h
    · exact ⟨0, h⟩
    · obtain ⟨i, hi⟩ := ih (Fin.tail x)
      exact ⟨i.succ, h.trans hi⟩

theorem minimum_price {A : Type} (price : A → Code) (n : ℕ) (x : Fin (n + 1) → A)
    (i : Fin (n + 1)) : (price (minimum price n x)).realValue ≤ (price (x i)).realValue := by
  induction n with
  | zero =>
    have h : i = 0 := Fin.ext (by have := i.isLt; omega)
    simp [h, minimum]
  | succ n ih =>
    have h := cheaper_price price (x 0) (minimum price n (Fin.tail x))
    refine Fin.cases h.1 (fun j => h.2.trans (ih (Fin.tail x) j)) i

def selectedTree {A : Type} (price : A → Code) (t : FiniteDrawTrees.Tree A) (n : ℕ) :
    FiniteDrawTrees.Tree A :=
  map (minimum price n) (samples t (n + 1))

def bitTree {A : Type} (price : A → Code) (t : FiniteDrawTrees.Tree A) (Q n confidence : ℕ) :
    FiniteDrawTrees.Tree A :=
  LazyFairBitTrees.lower (FairBitConfidence.trials ((n + 1) * Q) confidence)
    (selectedTree price t n)

theorem bitTree_binary {A : Type} (price : A → Code) (t : FiniteDrawTrees.Tree A) (Q n confidence : ℕ) :
    LazyFairBitTrees.Binary (bitTree price t Q n confidence) :=
  LazyFairBitTrees.lower_binary _ _

theorem bitTree_within {A : Type} (price : A → Code) (t : FiniteDrawTrees.Tree A)
    (Q n confidence width : ℕ) (h : Within Q t) (hw : LazyFairBitTrees.WidthsLE width t) :
    Within (((n + 1) * Q) * FairBitConfidence.trials ((n + 1) * Q) confidence * width)
      (bitTree price t Q n confidence) :=
  LazyFairBitTrees.lower_within (within_map (samples_within h (n + 1)) _)
    (LazyFairBitTrees.widths_map (samples_widths hw (n + 1)) _) _

private theorem selected_law {A : Type} [Fintype A] (price : A → Code)
    (t : FiniteDrawTrees.Tree A) (n : ℕ) :
    ideal (selectedTree price t n) = (sampleLaw (ideal t) (n + 1)).map (minimum price n) := by
  unfold selectedTree ideal
  rw [law_map]
  exact congrArg (fun p => p.map (minimum price n)) (samples_law t (n + 1))

theorem support_selected {A : Type} [Fintype A] (price : A → Code) (t : FiniteDrawTrees.Tree A)
    (Q n confidence : ℕ) :
    (ideal (bitTree price t Q n confidence)).support ⊆ (ideal t).support := by
  intro out hout
  have h := LazyFairBitTrees.lowered_support_subset_ideal _ (selectedTree price t n) hout
  rw [selected_law] at h
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  obtain ⟨i, hi⟩ := minimum_is_sample price n x
  rw [hi]
  exact (mem_support_sampleLaw_iff (ideal t) (n + 1) x).mp hx i

private theorem probability_selected_gt {A : Type} [Fintype A] (price : A → Code)
    (t : FiniteDrawTrees.Tree A) (n : ℕ) (B : ℝ) :
    probability (ideal (selectedTree price t n)) (fun x => B < ((price x).realValue : ℝ)) =
      probability (ideal t) (fun x => B < ((price x).realValue : ℝ)) ^ (n + 1) := by
  rw [selected_law]
  unfold probability
  rw [PMF.toOuterMeasure_map_apply]
  have h : (minimum price n) ⁻¹' {x | B < ((price x).realValue : ℝ)} =
      {s | ∀ i, B < ((price (s i)).realValue : ℝ)} := by
    ext s
    constructor
    · intro hs i
      exact hs.trans_le (NNReal.coe_le_coe.mpr (minimum_price price n s i))
    · intro hs
      obtain ⟨i, hi⟩ := minimum_is_sample price n s
      change B < ((price (minimum price n s)).realValue : ℝ)
      rw [hi]
      exact hs i
  rw [h]
  exact probability_all_samples (ideal t) (n + 1) (fun x => B < ((price x).realValue : ℝ))

theorem failure_le {A : Type} [Fintype A] (price : A → Code) (t : FiniteDrawTrees.Tree A)
    (Q n confidence : ℕ) (ht : Within Q t) (B : ℝ) (hB : 0 < B)
    (he : expectedCost (ideal t) (fun x => ((price x).realValue : ℝ)) ≤ B) :
    probability (ideal (bitTree price t Q n confidence))
        (fun x => 2 * B < ((price x).realValue : ℝ)) ≤
      ((1 : ℝ) / 2) ^ (n + 1) + ((1 : ℝ) / 2) ^ confidence := by
  have hdraw := within_map (samples_within ht (n + 1)) (minimum price n)
  have hbit := LazyFairBitTrees.lowered_event_le hdraw
    (FairBitConfidence.trials ((n + 1) * Q) confidence)
    (fun x => 2 * B < ((price x).realValue : ℝ))
  refine hbit.trans (add_le_add ?_ (FairBitConfidence.accumulated_failure _ _))
  change probability (ideal (selectedTree price t n))
    (fun x => 2 * B < ((price x).realValue : ℝ)) ≤ ((1 : ℝ) / 2) ^ (n + 1)
  rw [probability_selected_gt]
  apply pow_le_pow_left₀ (probability_nonneg _ _) _
  exact probability_cost_gt_twice_le_half (ideal t) _ (fun _ => NNReal.coe_nonneg _) hB he

theorem zero_price_on_support {A : Type} [Fintype A] (price : A → Code)
    (t : FiniteDrawTrees.Tree A) (Q n confidence : ℕ)
    (he : expectedCost (ideal t) (fun x => ((price x).realValue : ℝ)) ≤ 0)
    {out : A} (h : out ∈ (ideal (bitTree price t Q n confidence)).support) :
    ((price out).realValue : ℝ) = 0 :=
  cost_eq_zero_on_support (ideal t) _ (fun _ => NNReal.coe_nonneg _) he
    (support_selected price t Q n confidence h)

end DirectedFlowCutGap.EncodedAmplification
