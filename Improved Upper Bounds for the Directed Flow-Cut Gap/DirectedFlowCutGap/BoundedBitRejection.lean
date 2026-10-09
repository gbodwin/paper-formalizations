import DirectedFlowCutGap.FairBitWords

/-!
# Bounded fair-bit rejection with an explicit failure outcome

The input is a finite sequence of independent fair-bit words. The interpreter
returns the first legal index, or `none` after exhausting the supplied words.
Its actual consumed-bit count is bounded by the supplied trial budget times the
word width. The exact law has equal accepted atom masses and failure at most
`2^(-T)`. Failure is retained explicitly: this law is not called uniform.
-/
namespace DirectedFlowCutGap.BoundedBitRejection
open scoped BigOperators ENNReal
open FairBitWords FinitePermutationSampler FiniteAmplification

def Tape (n : ℕ) : ℕ → Type
  | 0 => Unit
  | T + 1 => Bits (width n) × Tape n T

instance tapeFintype (n : ℕ) : (T : ℕ) → Fintype (Tape n T)
  | 0 => inferInstanceAs (Fintype Unit)
  | T + 1 => @instFintypeProd (Bits (width n)) (Tape n T)
      inferInstance (tapeFintype n T)

structure Output (n : ℕ) where
  value : Option (Fin n)
  trials : ℕ
  bits : ℕ
deriving Repr, DecidableEq

/-- Each word is decoded once; a successful trial does not inspect the tail. -/
def run (n : ℕ) : (T : ℕ) → Tape n T → Output n
  | 0, _ => ⟨none,0,0⟩
  | T + 1, (t,rest) =>
      let w := FairBitWords.run (width n) t
      let x : Fin (bucket n) := ⟨w.1, run_value_lt (width n) t⟩
      match accept n x with
      | some a => ⟨some a,1,w.2⟩
      | none =>
          let r := run n T rest
          ⟨r.value,r.trials + 1,w.2 + r.bits⟩

/-- The proof-side result recursion uses the already proved positional bijection. -/
def result (n : ℕ) : (T : ℕ) → Tape n T → Option (Fin n)
  | 0, _ => none
  | T + 1, (t,rest) =>
      match accept n (decode (width n) t) with
      | some a => some a
      | none => result n T rest

theorem run_word_eq (n : ℕ) (t : Bits (width n)) :
    (⟨(FairBitWords.run (width n) t).1, run_value_lt (width n) t⟩ : Fin (bucket n)) =
      decode (width n) t := by
  apply Fin.ext
  exact run_value (width n) t

theorem run_result (n T : ℕ) (t : Tape n T) : (run n T t).value = result n T t := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rcases t with ⟨t,rest⟩
      simp only [run, run_word_eq, result]
      split <;> simp_all

theorem run_trials_le (n T : ℕ) (t : Tape n T) : (run n T t).trials ≤ T := by
  induction T with
  | zero => simp [run]
  | succ T ih =>
      rcases t with ⟨t,rest⟩
      simp only [run]
      split <;> simp_all

theorem run_bits_eq (n T : ℕ) (t : Tape n T) :
    (run n T t).bits = width n * (run n T t).trials := by
  induction T with
  | zero => simp [run]
  | succ T ih =>
      rcases t with ⟨t,rest⟩
      simp only [run]
      split <;> simp_all [Nat.mul_add, Nat.add_comm]

theorem run_bits_le (n T : ℕ) (t : Tape n T) : (run n T t).bits ≤ width n * T := by
  rw [run_bits_eq]
  exact Nat.mul_le_mul_left _ (run_trials_le n T t)

noncomputable section

/-- The literal independent word blocks, each itself made of independent fair bits. -/
def tapeLaw (n : ℕ) : (T : ℕ) → PMF (Tape n T)
  | 0 => PMF.pure ()
  | T + 1 => independent (bitsLaw (width n)) (tapeLaw n T)

/-- This recursive law retains the failure outcome instead of renormalizing it away. -/
def law (n : ℕ) : ℕ → PMF (Option (Fin n))
  | 0 => PMF.pure none
  | T + 1 => (trial n).bind fun x =>
      match x with
      | some a => PMF.pure (some a)
      | none => law n T

theorem result_law (n T : ℕ) : (tapeLaw n T).map (result n T) = law n T := by
  induction T with
  | zero =>
      change (PMF.pure ()).map (fun _ : Unit => (none : Option (Fin n))) = PMF.pure none
      exact PMF.pure_map _ _
  | succ T ih =>
      change (independent (bitsLaw (width n)) (tapeLaw n T)).map
          (fun t : Bits (width n) × Tape n T =>
            match accept n (decode (width n) t.1) with
            | some a => some a
            | none => result n T t.2) =
        (trial n).bind (fun x => match x with
          | some a => PMF.pure (some a)
          | none => law n T)
      rw [independent, PMF.map_bind, trial, PMF.bind_map, PMF.bind_map]
      simp only [PMF.map_comp, Function.comp_def]
      congr 1
      funext t
      cases h : accept n (decode (width n) t) with
      | none => simpa only [h] using ih
      | some a => exact PMF.map_const _ _

/-- Exact output law of the actual counted executable interpreter. -/
theorem run_law (n T : ℕ) :
    (tapeLaw n T).map (fun t => (run n T t).value) = law n T := by
  simpa only [run_result] using result_law n T

theorem law_succ_none (n T : ℕ) :
    law n (T + 1) none = trial n none * law n T none := by
  classical
  simp [law, PMF.bind_apply, tsum_fintype, Fintype.sum_option, PMF.pure_apply]

theorem law_succ_some (n T : ℕ) (a : Fin n) :
    law n (T + 1) (some a) = trial n (some a) + trial n none * law n T (some a) := by
  classical
  simp [law, PMF.bind_apply, tsum_fintype, Fintype.sum_option, PMF.pure_apply,
    add_comm]

theorem law_none (n T : ℕ) : law n T none = (trial n none) ^ T := by
  induction T with
  | zero => simp [law, PMF.pure_apply]
  | succ T ih => rw [law_succ_none, ih, pow_succ, mul_comm]

theorem law_failure_le {n : ℕ} (hn : 0 < n) (T : ℕ) :
    (law n T none).toReal ≤ ((1 : ℝ) / 2) ^ T := by
  rw [law_none, ENNReal.toReal_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (trial_reject_le_half hn) T

/-- Every accepted value has the same mass, before conditioning on success. -/
theorem law_some_equal (n T : ℕ) (a b : Fin n) :
    law n T (some a) = law n T (some b) := by
  induction T with
  | zero => simp [law, PMF.pure_apply]
  | succ T ih => rw [law_succ_some, law_succ_some, trial_some, trial_some, ih]

/-- The successful part is uniform with its actual total mass; failure remains
visible in the formula and is not identified with a primitive uniform draw. -/
theorem law_some_toReal (n T : ℕ) (a : Fin n) :
    (law n T (some a)).toReal = (1 - (law n T none).toReal) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt a.isLt)
  have h := sum_probability_toReal (law n T)
  rw [Fintype.sum_option] at h
  have he (b : Fin n) : (law n T (some b)).toReal = (law n T (some a)).toReal :=
    congrArg ENNReal.toReal (law_some_equal n T b a)
  simp_rw [he] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  apply (eq_div_iff hn.ne').mpr
  nlinarith

end
end DirectedFlowCutGap.BoundedBitRejection
