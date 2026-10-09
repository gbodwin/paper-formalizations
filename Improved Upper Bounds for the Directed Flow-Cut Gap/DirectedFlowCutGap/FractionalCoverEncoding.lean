import DirectedFlowCutGap.FractionalCoverCore

/-!
# Recorded amounts and a denominator-growth bound

This file bounds denominators along the actual rational recurrence in terms of
bounds on initial denominators and the finitely many cost-dependent update
factors. This is not a full bit-operation theorem: input-size bounds for these
parameters, normalized-cover numerators/denominators, summation intermediates,
comparison work, and the supplied oracle's encoding/cost remain obligations.
-/
namespace DirectedFlowCutGap.FractionalCover
open scoped BigOperators

/-- Exact trace amount, independently reconstructed from recorded events. -/
def traceTotal {m : ℕ} (es : List (Event m)) : ℚ := (es.map Event.amount).sum

def traceLoad {m : ℕ} (es : List (Event m)) (i : Fin m) : ℚ :=
  (es.map fun e => if i ∈ e.choice.column then e.amount else 0).sum

lemma run_trace_total {m : ℕ} (c : Row m) (oracle : Oracle m) (n : ℕ) :
    (run c oracle n).total = traceTotal (run c oracle n).events := by
  induction n with
  | zero => simp [run, start, traceTotal]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih
    · simp only [run, step, ite_eq_right hstop]
      simpa [traceTotal, add_comm] using congrArg
        (fun x => x + value c (oracle (run c oracle n).weights).bottleneck) ih

lemma run_trace_load {m : ℕ} (c : Row m) (oracle : Oracle m) (n : ℕ) (i : Fin m) :
    value (run c oracle n).loads i = traceLoad (run c oracle n).events i := by
  induction n with
  | zero => simp [run, start, traceLoad]
  | succ n ih =>
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih
    · simp only [run, step, ite_eq_right hstop]
      simpa [traceLoad, add_comm] using congrArg
        (fun x => x + if i ∈ (oracle (run c oracle n).weights).column then
          value c (oracle (run c oracle n).weights).bottleneck else 0) ih

/-- Each trace entry is an actual admissible column and its attained positive
bottleneck. These fields describe the event produced by this execution. -/
def EventValid {m : ℕ} (c : Row m) (columns : Set (Column m)) (e : Event m) : Prop :=
  e.choice.column ∈ columns ∧ e.choice.bottleneck ∈ e.choice.column ∧
  e.amount = value c e.choice.bottleneck ∧ 0 < e.amount ∧
  ∀ i ∈ e.choice.column, e.amount ≤ value c i

lemma run_events_valid {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (n : ℕ) :
    ∀ e ∈ (run c oracle n).events, EventValid c columns e := by
  induction n with
  | zero => simp [run, start]
  | succ n ih =>
    have hs := run_invariant c columns oracle hm hc ho n
    by_cases hstop : 1 ≤ objective c (run c oracle n).weights
    · simpa only [run, step, ite_eq_left hstop] using ih
    · simp only [run, step, ite_eq_right hstop]
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨ho.chosen_mem _ hs.positive, ho.bottleneck_mem _ hs.positive,
          rfl, hc _, ho.bottleneck_min _ hs.positive⟩
      · exact ih e he

lemma update_den_le {m : ℕ} (c y : Row m) (q : Choice m) (F : ℕ)
    (hF : 1 ≤ F)
    (hf : ∀ i j : Fin m, (1 + value c j / (2 * value c i)).den ≤ F) (i : Fin m) :
    (value (update c y q) i).den ≤ (value y i).den * F := by
  simp only [update, value_ofFn]
  split_ifs
  · exact (Nat.le_of_dvd (Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _)) (Rat.mul_den_dvd _ _)).trans
      (Nat.mul_le_mul_left _ (hf i q.bottleneck))
  · simpa only [Nat.mul_one] using Nat.mul_le_mul_left (value y i).den hF

lemma step_den_le {m : ℕ} (c : Row m) (oracle : Oracle m) (s : State m)
    (F : ℕ) (hF : 1 ≤ F)
    (hf : ∀ i j : Fin m, (1 + value c j / (2 * value c i)).den ≤ F) (i : Fin m) :
    (value (step c oracle s).weights i).den ≤ (value s.weights i).den * F := by
  by_cases hstop : 1 ≤ objective c s.weights
  · simp only [step, ite_eq_left hstop]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (value s.weights i).den hF
  · simp only [step, ite_eq_right hstop]
    exact update_den_le c s.weights _ F hF hf i

/-- Denominator magnitudes grow multiplicatively, so their bit lengths grow
linearly in the actual update fuel when the factor width is bounded. -/
theorem run_den_le {m : ℕ} (c : Row m) (oracle : Oracle m)
    (A F : ℕ) (hA : ∀ i, (value (initial c) i).den ≤ A) (hF : 1 ≤ F)
    (hf : ∀ i j : Fin m, (1 + value c j / (2 * value c i)).den ≤ F)
    (n : ℕ) (i : Fin m) : (value (run c oracle n).weights i).den ≤ A * F^n := by
  induction n with
  | zero => simpa [run, start] using hA i
  | succ n ih =>
    calc
      _ ≤ (value (run c oracle n).weights i).den * F :=
        step_den_le c oracle _ F hF hf i
      _ ≤ (A * F^n) * F := Nat.mul_le_mul_right F ih
      _ = A * F^(n+1) := by rw [pow_succ, Nat.mul_assoc]

/-- Explicit binary bound with input/factor widths as visible obligations. -/
theorem run_den_bits {m : ℕ} (c : Row m) (oracle : Oracle m)
    (a f : ℕ) (hA : ∀ i, (value (initial c) i).den ≤ 2^a)
    (hf : ∀ i j : Fin m, (1 + value c j / (2 * value c i)).den ≤ 2^f)
    (n : ℕ) (i : Fin m) :
    Nat.size (value (run c oracle n).weights i).den ≤ a + n*f + 1 := by
  have h := run_den_le c oracle (2^a) (2^f) hA (Nat.succ_le_of_lt (pow_pos (by decide : (0 : ℕ) < 2) f)) hf n i
  have heq : 2^a * (2^f)^n = 2^(a+n*f) := by
    rw [← pow_mul, ← pow_add, Nat.mul_comm f n]
  rw [heq] at h
  exact (Nat.size_le_size h).trans_eq Nat.size_pow

lemma numerator_le_of_bounded {q : ℚ} (hq : 0 < q) (B : ℕ) (hB : q ≤ B) :
    q.num.natAbs ≤ B * q.den := by
  have hn : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have heq : (q.num.natAbs : ℚ) = q * (q.den : ℚ) := by
    calc
      _ = (q.num : ℚ) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hn
      _ = q * (q.den : ℚ) := by
        exact (div_eq_iff (by exact_mod_cast q.den_nz : (q.den : ℚ) ≠ 0)).mp (Rat.num_div_den q)
  have h := mul_le_mul_of_nonneg_right hB (show (0 : ℚ) ≤ q.den by positivity)
  rw [← heq] at h
  exact_mod_cast h

/-- A lower input-cost magnitude bound supplies a numerator bound for every
stored current weight, in addition to the denominator bound above. -/
theorem run_num_bits {m : ℕ} (c : Row m) (columns : Set (Column m))
    (oracle : Oracle m) (hm : 0 < m) (hc : ∀ i, 0 < value c i)
    (ho : OracleCorrect c columns oracle) (a f b : ℕ)
    (hA : ∀ i, (value (initial c) i).den ≤ 2^a)
    (hf : ∀ i j : Fin m, (1 + value c j / (2 * value c i)).den ≤ 2^f)
    (hb : ∀ i, (3 / 2 : ℚ) ≤ value c i * (2^b : ℕ))
    (n : ℕ) (i : Fin m) :
    Nat.size (value (run c oracle n).weights i).num.natAbs ≤ b + a + n*f + 1 := by
  have hs := run_invariant c columns oracle hm hc ho n
  have hw : value (run c oracle n).weights i ≤ (2^b : ℕ) := by
    exact (mul_le_mul_iff_right₀ (hc i)).mp ((hs.scaled_lt i).le.trans (hb i))
  have hn := numerator_le_of_bounded (hs.positive i) (2^b) hw
  have hd := run_den_le c oracle (2^a) (2^f) hA (Nat.succ_le_of_lt (pow_pos (by decide : (0 : ℕ) < 2) f)) hf n i
  have hpow : 2^b * (2^a * (2^f)^n) = 2^(b+a+n*f) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    simp only [Nat.mul_comm f n, Nat.add_assoc]
  have h := hn.trans (Nat.mul_le_mul_left (2^b) hd)
  rw [hpow] at h
  exact (Nat.size_le_size h).trans_eq Nat.size_pow

end DirectedFlowCutGap.FractionalCover
