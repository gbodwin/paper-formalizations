import DirectedFlowCutGap.FractionalCoverAnalysis
import DirectedFlowCutGap.FractionalCoverEncoding

/-!
# Pathwise weighted packing with approximate cut choices

This component uses the actual rational update and retained events. The chosen
oracle may change at every round. Its contract is required only at the reached,
active state, and requires the all-cost bound, not exact minimum-column selection.
Thus this is a pathwise theorem, with no independence or success-probability claim.
An efficient oracle implementation, a fair-bit weighted sampler, zero-cost entry
branches, and the unconditional failure/runtime composition remain separate.
-/
namespace DirectedFlowCutGap.ApproximatePackingTrace
open scoped BigOperators
open FractionalCover

/-- A round-indexed execution retains all fields of the existing rational step. -/
def run {m : ℕ} (c : Row m) (oracle : ℕ → Oracle m) : ℕ → State m
  | 0 => start c (oracle 0)
  | n + 1 => step c (oracle n) (run c oracle n)

/-- Only choices actually used by active rounds are constrained. -/
structure ChoicesCorrect {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (α : ℝ) : Prop where
  chosen_mem : ∀ n, objective c (run c oracle n).weights < 1 →
    (oracle n (run c oracle n).weights).column ∈ columns
  bottleneck_mem : ∀ n, objective c (run c oracle n).weights < 1 →
    (oracle n (run c oracle n).weights).bottleneck ∈
      (oracle n (run c oracle n).weights).column
  bottleneck_min : ∀ n, objective c (run c oracle n).weights < 1 →
    ∀ i ∈ (oracle n (run c oracle n).weights).column,
      value c (oracle n (run c oracle n).weights).bottleneck ≤ value c i
  budget : ∀ n, objective c (run c oracle n).weights < 1 →
    (length (run c oracle n).weights (oracle n (run c oracle n).weights).column : ℝ) ≤
      α * (objective c (run c oracle n).weights : ℝ)

/-- This invariant deliberately makes no feasible-cover or exact-oracle claim. -/
structure Invariant {m : ℕ} (c : Row m) (α : ℝ) (s : State m) : Prop where
  positive : ∀ i, 0 < value s.weights i
  initial_le : ∀ i, delta m ≤ value c i * value s.weights i
  scaled_lt : ∀ i, value c i * value s.weights i < 3 / 2
  potential : 2 * α⁻¹ * (Real.log (objective c s.weights : ℝ) -
      Real.log (objective c (initial c) : ℝ)) ≤ (s.total : ℝ)
  load : ∀ i, (value s.loads i : ℝ) ≤ 3 * (value c i : ℝ) *
    (Real.log (value c i * value s.weights i : ℚ) - Real.log (delta m : ℝ))

lemma start_invariant {m : ℕ} (c : Row m) (oracle : ℕ → Oracle m)
    (hm : 0 < m) (hc : ∀ i, 0 < value c i) (α : ℝ) :
    Invariant c α (run c oracle 0) := by
  refine ⟨initial_pos c hm hc, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (initial_scaled c hc i).ge
  · intro i
    change value c i * value (initial c) i < 3 / 2
    rw [initial_scaled c hc]
    linarith [delta_le hm]
  · simp [run, start]
  · intro i
    simp [run, start, initial_scaled c hc]

lemma step_invariant {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    {α : ℝ} (hα : 0 < α) (ho : ChoicesCorrect c columns oracle α) (n : ℕ)
    (hs : Invariant c α (run c oracle n)) :
    Invariant c α (run c oracle (n+1)) := by
  by_cases hstop : 1 ≤ objective c (run c oracle n).weights
  · simpa only [run, step, ite_eq_left hstop] using hs
  · have hactive := lt_of_not_ge hstop
    have hy := hs.positive
    have hlen := length_pos hy ⟨_, ho.bottleneck_mem n hactive⟩
    have hobj := objective_pos c _ hm hc hy
    simp only [run, step, ite_eq_right hstop]
    refine ⟨update_pos c _ _ hc hy, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (hs.initial_le i).trans (mul_le_mul_of_nonneg_left
        (update_mono c _ _ hc (fun i => (hy i).le) i) (hc i).le)
    · exact update_scaled_lt c _ _ hc hy (ho.bottleneck_min n hactive) hactive
    · have ha : (0 : ℝ) < length (run c oracle n).weights
          (oracle n (run c oracle n).weights).column := by exact_mod_cast hlen
      have hD : (0 : ℝ) < objective c (run c oracle n).weights := by exact_mod_cast hobj
      have hz : α⁻¹ ≤ (objective c (run c oracle n).weights : ℝ) /
          (length (run c oracle n).weights (oracle n (run c oracle n).weights).column : ℝ) := by
        apply (le_div_iff₀ ha).2
        have hb := mul_le_mul_of_nonneg_left (ho.budget n hactive) (inv_pos.mpr hα).le
        simpa [← mul_assoc, ne_of_gt hα] using hb
      have hp := potential_step hD ha
        (show 0 ≤ (value c (oracle n (run c oracle n).weights).bottleneck : ℝ) by
          exact_mod_cast (hc _).le) (inv_pos.mpr hα) hz
      have heq : (objective c (update c (run c oracle n).weights
          (oracle n (run c oracle n).weights)) : ℝ) =
          (objective c (run c oracle n).weights : ℝ) +
          (value c (oracle n (run c oracle n).weights).bottleneck : ℝ) *
          (length (run c oracle n).weights (oracle n (run c oracle n).weights).column : ℝ) / 2 := by
        exact_mod_cast objective_update c _ _ hc
      dsimp
      rw [heq]
      push_cast
      linarith [hs.potential]
    · intro i
      have hci : (0 : ℝ) < value c i := by exact_mod_cast hc i
      have hxi : (0 : ℝ) < (value c i * value (run c oracle n).weights i : ℚ) := by
        exact_mod_cast mul_pos (hc i) (hy i)
      dsimp
      simp only [value_ofFn]
      by_cases hi : i ∈ (oracle n (run c oracle n).weights).column
      · rw [ite_eq_left hi]
        have hl := load_step hci hxi
          (show 0 ≤ (value c (oracle n (run c oracle n).weights).bottleneck : ℝ) by
            exact_mod_cast (hc _).le)
          (show (value c (oracle n (run c oracle n).weights).bottleneck : ℝ) ≤ value c i by
            exact_mod_cast ho.bottleneck_min n hactive i hi)
        have heq : ((value c i * value (update c (run c oracle n).weights
            (oracle n (run c oracle n).weights)) i : ℚ) : ℝ) =
            ((value c i * value (run c oracle n).weights i : ℚ) : ℝ) *
              (1 + (value c (oracle n (run c oracle n).weights).bottleneck : ℝ) /
                (2 * (value c i : ℝ))) := by
          simp only [update, value_ofFn, ite_eq_left hi]
          push_cast
          ring
        rw [heq]
        push_cast at hl ⊢
        have hold := hs.load i
        push_cast at hold
        linarith
      · rw [ite_eq_right hi]
        simpa [update, hi] using hs.load i

lemma run_invariant {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    {α : ℝ} (hα : 0 < α) (ho : ChoicesCorrect c columns oracle α) (n : ℕ) :
    Invariant c α (run c oracle n) := by
  induction n with
  | zero => exact start_invariant c oracle hm hc α
  | succ n ih => exact step_invariant c columns oracle hm hc hα ho n ih

lemma run_progress {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    {α : ℝ} (hα : 0 < α) (ho : ChoicesCorrect c columns oracle α) (n : ℕ) :
    1 ≤ objective c (run c oracle n).weights ∨
      objective c (initial c) + n * (delta m / 2) ≤ objective c (run c oracle n).weights := by
  induction n with
  | zero => right; simp [run, start]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · left
      simp [run, step, hstop]
    · right
      have hp := ih.resolve_left hstop
      have hs := run_invariant c columns oracle hm hc hα ho n
      have hi := objective_increment c _ (oracle n _) hc hs.positive
        (ho.bottleneck_mem n (lt_of_not_ge hstop)) hs.initial_le
      simp only [run, step, ite_eq_right hstop]
      push_cast
      linarith

/-- The number of rounds is independent of the smallest positive input weight. -/
theorem stopped {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    {α : ℝ} (hα : 0 < α) (ho : ChoicesCorrect c columns oracle α) :
    1 ≤ objective c (run c oracle (fuel m)).weights := by
  rcases run_progress c columns oracle hm hc hα ho (fuel m) with h | h
  · exact h
  · have hf : (fuel m : ℚ) * (delta m / 2) = 1 := by
      unfold fuel delta
      push_cast
      field_simp [ne_of_gt (show (0 : ℚ) < m by exact_mod_cast hm)]
    rw [hf] at h
    exact le_trans (by linarith [objective_pos c _ hm hc (initial_pos c hm hc)]) h

lemma run_event_count {m : ℕ} (c : Row m) (oracle : ℕ → Oracle m) (n : ℕ) :
    (run c oracle n).events.length ≤ n := by
  induction n with
  | zero => simp [run, start]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih.trans (Nat.le_succ n)
    · simpa only [run, step, ite_eq_right hstop, List.length_cons] using Nat.succ_le_succ ih

lemma run_trace_total {m : ℕ} (c : Row m) (oracle : ℕ → Oracle m) (n : ℕ) :
    (run c oracle n).total = traceTotal (run c oracle n).events := by
  induction n with
  | zero => simp [run, start, traceTotal]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih
    · simp only [run, step, ite_eq_right hstop]
      simpa [traceTotal, add_comm] using congrArg
        (fun x => x + value c (oracle n (run c oracle n).weights).bottleneck) ih

lemma run_trace_load {m : ℕ} (c : Row m) (oracle : ℕ → Oracle m) (n : ℕ) (i : Fin m) :
    value (run c oracle n).loads i = traceLoad (run c oracle n).events i := by
  induction n with
  | zero => simp [run, start, traceLoad]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih
    · simp only [run, step, ite_eq_right hstop]
      simpa [traceLoad, add_comm] using congrArg
        (fun x => x + if i ∈ (oracle n (run c oracle n).weights).column then
          value c (oracle n (run c oracle n).weights).bottleneck else 0) ih

lemma run_events_valid {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (hc : ∀ i, 0 < value c i)
    {α : ℝ} (ho : ChoicesCorrect c columns oracle α) (n : ℕ) :
    ∀ e ∈ (run c oracle n).events, EventValid c columns e := by
  induction n with
  | zero => simp [run, start]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih
    · simp only [run, step, ite_eq_right hstop]
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨ho.chosen_mem n (lt_of_not_ge hstop),
          ho.bottleneck_mem n (lt_of_not_ge hstop), rfl, hc _,
          ho.bottleneck_min n (lt_of_not_ge hstop)⟩
      · exact ih e he

lemma total_lower {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    {α : ℝ} (hα : 0 < α) (ho : ChoicesCorrect c columns oracle α) :
    2 * α⁻¹ * Real.log (3 * (m : ℝ) / 2) ≤ (run c oracle (fuel m)).total := by
  have hs := run_invariant c columns oracle hm hc hα ho (fuel m)
  have hstop : (1 : ℝ) ≤ (objective c (run c oracle (fuel m)).weights : ℝ) := by
    exact_mod_cast stopped c columns oracle hm hc hα ho
  have hlog := Real.log_nonneg hstop
  have hinit : Real.log (objective c (initial c) : ℝ) = -Real.log (3 * (m : ℝ) / 2) := by
    rw [objective_initial c hc]
    push_cast
    linarith [(log_parameters hm).1]
  have hp := hs.potential
  rw [hinit] at hp
  nlinarith [mul_nonneg (inv_pos.mpr hα).le hlog]

lemma load_upper {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    {α : ℝ} (hα : 0 < α) (ho : ChoicesCorrect c columns oracle α) (i : Fin m) :
    (value (run c oracle (fuel m)).loads i : ℝ) ≤
      6 * Real.log (3 * (m : ℝ) / 2) * (value c i : ℝ) := by
  have hs := run_invariant c columns oracle hm hc hα ho (fuel m)
  have hx : (0 : ℝ) < (value c i * value (run c oracle (fuel m)).weights i : ℚ) := by
    exact_mod_cast mul_pos (hc i) (hs.positive i)
  have hu : ((value c i * value (run c oracle (fuel m)).weights i : ℚ) : ℝ) ≤ 3 / 2 := by
    have hh : ((value c i * value (run c oracle (fuel m)).weights i : ℚ) : ℝ) ≤ ((3/2 : ℚ) : ℝ) := by
      exact_mod_cast (hs.scaled_lt i).le
    norm_num at hh ⊢
    exact hh
  have hl := Real.log_le_log hx hu
  have hmul := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hl (Real.log (delta m : ℝ)))
    (show 0 ≤ 3 * (value c i : ℝ) by exact_mod_cast (mul_pos (by norm_num : (0 : ℚ) < 3) (hc i)).le)
  rw [(log_parameters hm).2] at hmul
  have h := (hs.load i).trans hmul
  nlinarith

/-- Normalizing the actual retained positive event amounts gives the desired
pathwise marginal bound. This is not a claim about an implemented sampler. -/
theorem trace_marginal_le {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : ℕ → Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    {α : ℝ} (hα : 0 < α) (ho : ChoicesCorrect c columns oracle α) (i : Fin m) :
    0 < traceTotal (run c oracle (fuel m)).events ∧
    (traceLoad (run c oracle (fuel m)).events i : ℝ) /
      (traceTotal (run c oracle (fuel m)).events : ℝ) ≤ 3 * α * (value c i : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK : 0 < Real.log (3 * (m : ℝ) / 2) := Real.log_pos (by linarith)
  have hlow := total_lower c columns oracle hm hc hα ho
  have htotal : (0 : ℝ) < (run c oracle (fuel m)).total :=
    lt_of_lt_of_le (by positivity) hlow
  have hupper := load_upper c columns oracle hm hc hα ho i
  have hci : (0 : ℝ) < value c i := by exact_mod_cast hc i
  have hmul := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 3 * α * (value c i : ℝ) by positivity)
  have heq : (3 * α * (value c i : ℝ)) * (2 * α⁻¹ * Real.log (3 * (m : ℝ) / 2)) =
      6 * Real.log (3 * (m : ℝ) / 2) * (value c i : ℝ) := by
    field_simp [ne_of_gt hα]
    <;> ring
  rw [heq] at hmul
  have hbound := (div_le_iff₀ htotal).2 (hupper.trans hmul)
  rw [run_trace_load, run_trace_total] at hbound
  have hp : (0 : ℝ) < (traceTotal (run c oracle (fuel m)).events : ℝ) := by
    simpa [run_trace_total] using htotal
  exact ⟨by exact_mod_cast hp, hbound⟩

end DirectedFlowCutGap.ApproximatePackingTrace
