import DirectedFlowCutGap.BitSamplerCoupling

/-!
# Bounded adaptive programs with finite draws

The index bounds the number of calls on every branch, including branches caused
by a legal default after bounded rejection. Each draw may choose its positive
bound from the full prior history. Replacing every uniform draw by the explicit
bounded fair-bit/default law changes any output event by at most the call bound
times the per-call failure bound.

This is a generic finite-program theorem. The concrete graph controller must
still be translated into this interface and its input/bit-operation costs
composed; those obligations are not assumptions hidden in this theorem.
-/
namespace DirectedFlowCutGap.BoundedDrawPrograms
open scoped BigOperators ENNReal
open FiniteAmplification BitSamplerCoupling

/-- A finite adaptive draw program with a bound on every execution branch. -/
inductive Program (A : Type) : ℕ → Type where
  | pure {q : ℕ} (a : A) : Program A q
  | draw {q : ℕ} (n : ℕ) (positive : 0 < n)
      (next : Fin n → Program A q) : Program A (q + 1)

/-- The same executable interpreter can use any monadic finite-draw adapter. -/
def execute {A : Type} {m : Type → Type} [Monad m]
    (sample : (n : ℕ) → 0 < n → m (Fin n)) :
    {q : ℕ} → Program A q → m A
  | _, .pure a => pure a
  | _, .draw n hn next => do
      let a ← sample n hn
      execute sample (next a)

noncomputable section
open scoped Classical

variable {A : Type} [Fintype A]

def ideal : {q : ℕ} → Program A q → PMF A
  | _, .pure a => PMF.pure a
  | _, .draw n hn next =>
      haveI : NeZero n := ⟨hn.ne'⟩
      (PMF.uniformOfFintype (Fin n)).bind (fun a => ideal (next a))

def actual (T : ℕ) : {q : ℕ} → Program A q → PMF A
  | _, .pure a => PMF.pure a
  | _, .draw n hn next =>
      haveI : NeZero n := ⟨hn.ne'⟩
      (fallback n T).bind (fun a => actual T (next a))

/-- This adapter samples the literal independent fair-bit tape and runs its
counted bounded-rejection/default interpreter. Constructing the entire tape
would cost all its bits, even if the interpreter consumes only a prefix. -/
def tapeAdapter (T n : ℕ) (hn : 0 < n) : PMF (Fin n) :=
  haveI : NeZero n := ⟨hn.ne'⟩
  (BoundedBitRejection.tapeLaw n T).map (fun t => (fallbackRun n T t).value)

theorem tapeAdapter_eq (T n : ℕ) (hn : 0 < n) :
    tapeAdapter T n hn = @fallback n T ⟨hn.ne'⟩ := by
  let : NeZero n := ⟨hn.ne'⟩
  exact fallbackRun_law n T

omit [Fintype A] in
/-- The biased law is the law of the actual executable tape adapter. -/
theorem execute_tapeAdapter (T : ℕ) {q : ℕ} (p : Program A q) :
    execute (tapeAdapter T) p = actual T p := by
  induction p with
  | pure a => rfl
  | @draw q n hn next ih =>
      simp only [execute, actual, tapeAdapter_eq]
      congr 1
      funext a
      exact ih a

theorem probability_le_one (p : PMF A) (P : A → Prop) :
    probability p P ≤ 1 := by
  rw [probability_eq_expected_indicator]
  exact expected_indicator_le_one p P

theorem probability_bind {B : Type} [Fintype B] (p : PMF B)
    (f : B → PMF A) (P : A → Prop) :
    probability (p.bind f) P = expectedCost p (fun b => probability (f b) P) := by
  simp_rw [probability_eq_expected_indicator]
  exact expectedCost_bind p f _

/-- The additive error holds for every history-dependent bound and continuation.
There is no comparison of actual and ideal bounds after a disagreement. -/
theorem event_le (T : ℕ) {q : ℕ} (p : Program A q) (P : A → Prop) :
    probability (actual T p) P ≤ probability (ideal p) P +
      (q : ℝ) * ((1 : ℝ) / 2) ^ T := by
  induction p with
  | @pure q a =>
      simp only [actual, ideal]
      exact le_add_of_nonneg_right (by positivity)
  | @draw q n hn next ih =>
      let : NeZero n := ⟨hn.ne'⟩
      rw [actual, ideal, probability_bind, probability_bind]
      have step :
          expectedCost (fallback n T) (fun a => probability (actual T (next a)) P) ≤
          expectedCost (fallback n T) (fun a => probability (ideal (next a)) P) +
            (q : ℝ) * ((1 : ℝ) / 2) ^ T := by
        unfold expectedCost
        have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
          (fun a _ => mul_le_mul_of_nonneg_left (ih a)
            (ENNReal.toReal_nonneg (a := fallback n T a)))
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
          sum_probability_toReal, one_mul] at hsum
        exact hsum
      have transfer := fallback_expected_le n T
        (fun a => probability (ideal (next a)) P)
        (fun a => probability_nonneg _ _) (fun a => probability_le_one _ _)
      push_cast
      nlinarith [step, transfer]

/-- Depth zero incurs no random-bit approximation error. -/
theorem event_le_zero (T : ℕ) (p : Program A 0) (P : A → Prop) :
    probability (actual T p) P ≤ probability (ideal p) P := by
  simpa using event_le T p P

end
end DirectedFlowCutGap.BoundedDrawPrograms
