import DirectedFlowCutGap.EncodedRoundingRepetition

/-!
# Exact failure amplification for the actual repeated selector

The complete output records contain unbounded counters and need not form a
finite type. This proof uses PMF outer measures directly, so it does not assume
finite support or a finite state/history space. The recorded sample-list law
and actual first-on-ties selector give the exact power law for any single-draw
threshold event. In particular biased typed draws can be amplified once their
own one-draw failure probability has been bounded.

These are probability joins for the existing executable repetition. No new
sampler or selector body is introduced. A one-draw graph-query quality bound,
finite-bit coupling and the whole runtime/storage substitution remain separate.
-/
namespace DirectedFlowCutGap.EncodedRoundingProbability
open EncodedRoundingEntry EncodedRoundingRepetition
open scoped ENNReal
variable {n : ℕ}
noncomputable section
private theorem pmf_pure {A : Type*} (a : A) : (pure a : PMF A)=PMF.pure a := rfl

theorem listLaw_all (draw : PMF (Output n)) (P : Output n → Prop) (k : Nat) :
    (listLaw draw k).toOuterMeasure {xs | ∀ x ∈ xs, P x} =
      (draw.toOuterMeasure {x | P x})^k := by
  classical
  induction k with
  | zero => simp [listLaw,pmf_pure]
  | succ k ih =>
      change (draw.bind fun x => (listLaw draw k).map (List.cons x)).toOuterMeasure _ = _
      rw [PMF.toOuterMeasure_bind_apply]
      have sectionProbability (x : Output n) :
          ((listLaw draw k).map (List.cons x)).toOuterMeasure {xs | ∀ a ∈ xs, P a} =
            if P x then (draw.toOuterMeasure {x | P x})^k else 0 := by
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hx : P x
        · have he : List.cons x ⁻¹' {xs : List (Output n) | ∀ a ∈ xs, P a} =
              {xs | ∀ a ∈ xs, P a} := by ext xs; simp [hx]
          rw [he,ih,ite_eq_left hx]
        · have he : List.cons x ⁻¹' {xs : List (Output n) | ∀ a ∈ xs, P a} = ∅ := by
            ext xs; simp [hx]
          rw [he,ite_eq_right hx]
          simp
      simp_rw [sectionProbability]
      rw [pow_succ']
      conv => rhs; lhs; rw [PMF.toOuterMeasure_apply]
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro x
      by_cases hx : P x <;> simp [hx]

/-- The event identity refers to the actual selected record on its support;
no equality with a different argmin's tie choice is required. -/
theorem repeat_threshold_probability (draw : PMF (Output n)) (extra threshold : ℕ) :
    (repeatDraws draw extra).toOuterMeasure {r | threshold < r.selected.vertices.length} =
      (draw.toOuterMeasure {o | threshold < o.vertices.length})^(extra+1) := by
  calc
    _ = (repeatDraws draw extra).toOuterMeasure
        (Result.samples ⁻¹' {xs | ∀ o ∈ xs, threshold < o.vertices.length}) := by
      apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
      ext r
      constructor
      · intro ⟨hr,hs⟩
        exact ⟨(repeat_threshold_iff draw extra threshold hs).mp hr,hs⟩
      · intro ⟨hr,hs⟩
        exact ⟨(repeat_threshold_iff draw extra threshold hs).mpr hr,hs⟩
    _ = ((repeatDraws draw extra).map Result.samples).toOuterMeasure
        {xs | ∀ o ∈ xs, threshold < o.vertices.length} := by
      rw [PMF.toOuterMeasure_map_apply]
    _ = _ := by rw [repeat_projection,listLaw_all]

/-- The same exact equation for the concrete guarded rounding entry. -/
theorem run_threshold_probability {L : ℕ}
    (sample : (a : RetainedGridState.PairFlags n) → PMF (RetainedTapeInput.Tape L a × ℕ))
    (adjacency : RetainedGridState.PairFlags n) (hL : 0<L) (extra threshold : ℕ) :
    (EncodedRoundingRepetition.run sample adjacency hL extra).toOuterMeasure
        {r | threshold < r.selected.vertices.length} =
      ((EncodedAllRegimeRounding.run sample adjacency hL).toOuterMeasure
        {o | threshold < o.vertices.length})^(extra+1) :=
  repeat_threshold_probability (EncodedAllRegimeRounding.run sample adjacency hL) extra threshold

end
end DirectedFlowCutGap.EncodedRoundingProbability
