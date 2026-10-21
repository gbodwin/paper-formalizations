import LightEFTFlatTapeStage.FlatTapeLaw
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp

/-! Unelaborated source checkpoint. Randomness is a fresh fair Boolean at each
program step, explicitly composed by Law.bind. No uniform Fin q draw is a
primitive. Almost-sure termination is stated in finite-prefix operational
semantics; no separate infinite-stream measure/refinement is asserted. Costs
below count consumed fair bits/reads, not arithmetic bit operations. -/
namespace LightEFTSpanners.FairBitDigit
open Finset FiniteProbability Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

def half : ℝ := 1/2

noncomputable def fairCoin : Law Bool where
  mass _ := half
  nonneg _ := by norm_num [half]
  total := by norm_num [half]

def digit (q : ℕ) (r : Fin q) : Bool := decide (q ≤ 2*r.val)

def nextRemainder (q : ℕ) (hq : 0 < q) (r : Fin q) : Fin q :=
  ⟨(2*r.val) % q, Nat.mod_lt _ hq⟩

def remainder (q : ℕ) (hq : 0 < q) : Fin q → ℕ → Fin q
  | r, 0 => r
  | r, t+1 => remainder q hq (nextRemainder q hq r) t

def outputAt (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ) : Bool :=
  digit q (remainder q hq r t)

def transcript (q : ℕ) (hq : 0 < q) : Fin q → ℕ → List Bool
  | r, 0 => [!digit q r]
  | r, t+1 => digit q r :: transcript q hq (nextRemainder q hq r) t

/-- Reads a consecutive prefix and returns output, read count and untouched suffix.
None means finite input exhaustion. The unbounded sampler is its fair-bit tree. -/
def run (q : ℕ) (hq : 0 < q) : Fin q → List Bool → Option (Bool × ℕ × List Bool)
  | _, [] => none
  | r, b::bs =>
    if b = digit q r then
      (run q hq (nextRemainder q hq r) bs).map
        (fun result => (result.1, result.2.1+1, result.2.2))
    else some (digit q r, 1, bs)

theorem transcript_length (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ) :
    (transcript q hq r t).length = t+1 := by
  induction t generalizing r with
  | zero => simp [transcript]
  | succ t ih => simp [transcript, ih]

theorem run_transcript (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ)
    (suffix : List Bool) :
    run q hq r (transcript q hq r t ++ suffix) =
      some (outputAt q hq r t, t+1, suffix) := by
  induction t generalizing r with
  | zero => cases hd : digit q r <;> simp [transcript, run, outputAt, remainder, hd]
  | succ t ih =>
    simp only [transcript, List.cons_append, run, if_pos rfl]
    rw [ih]
    rfl

def fraction (q : ℕ) (r : Fin q) : ℝ := (r.val:ℝ)/(q:ℝ)

theorem fraction_nonneg (q : ℕ) (hq : 0 < q) (r : Fin q) : 0 ≤ fraction q r := by
  exact div_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hq.le)

theorem fraction_lt_one (q : ℕ) (hq : 0 < q) (r : Fin q) : fraction q r < 1 := by
  apply (div_lt_one (show (0:ℝ) < q by exact_mod_cast hq)).mpr
  exact_mod_cast r.isLt

theorem digit_fraction (q : ℕ) (hq : 0 < q) (r : Fin q) :
    fraction q r = (if digit q r then half else 0) +
      half * fraction q (nextRemainder q hq r) := by
  have hrlt := r.isLt
  have hs : 2*r.val = (if digit q r then q else 0) +
      (nextRemainder q hq r).val := by
    by_cases h : q ≤ 2*r.val
    · have hn : (nextRemainder q hq r).val = 2*r.val-q := by
        dsimp [nextRemainder]
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      simp only [digit, h, decide_true, Bool.true_eq_true, if_true, hn]
      omega
    · have hn : (nextRemainder q hq r).val = 2*r.val := by
        exact Nat.mod_eq_of_lt (by omega)
      simp [digit, h, hn]
  have hr := congrArg (fun x : ℕ => (x:ℝ)) hs
  push_cast at hr
  have hq0 : (q:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hq)
  unfold fraction half
  cases hd : digit q r <;> simp [hd] at hr ⊢ <;> field_simp [hq0] <;> nlinarith

/-- Finite-horizon probabilistic semantics of the same bit branch.
Every continuation consumes a NEW fairCoin, even when the remainder is zero. -/
noncomputable def fuelLaw (q : ℕ) (hq : 0 < q) : Fin q → ℕ → Law (Option Bool)
  | _, 0 => Law.pure none
  | r, t+1 => fairCoin.bind fun b =>
      if b = digit q r then fuelLaw q hq (nextRemainder q hq r) t
      else Law.pure (some (digit q r))

theorem fuel_wait_succ (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ) :
    (fuelLaw q hq r (t+1)).mass none =
      half * (fuelLaw q hq (nextRemainder q hq r) t).mass none := by
  cases hd : digit q r <;> simp [fuelLaw, fairCoin, Law.bind, Law.pure, hd] <;> ring

theorem fuel_true_succ (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ) :
    (fuelLaw q hq r (t+1)).mass (some true) =
      (if digit q r then half else 0) +
      half * (fuelLaw q hq (nextRemainder q hq r) t).mass (some true) := by
  cases hd : digit q r <;> simp [fuelLaw, fairCoin, Law.bind, Law.pure, hd] <;> ring

theorem fuel_wait_mass (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ) :
    (fuelLaw q hq r t).mass none = half^t := by
  induction t generalizing r with
  | zero => simp [fuelLaw, Law.pure]
  | succ t ih => rw [fuel_wait_succ, ih, pow_succ]; ring

theorem fuel_true_formula (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ) :
    (fuelLaw q hq r t).mass (some true) =
      fraction q r - half^t * fraction q (remainder q hq r t) := by
  induction t generalizing r with
  | zero => simp [fuelLaw, Law.pure, remainder]
  | succ t ih =>
    rw [fuel_true_succ, ih, digit_fraction q hq r, pow_succ]
    simp only [remainder]
    ring

theorem half_pow_tendsto_zero : Tendsto (fun t : ℕ => half^t) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num [half]) (by norm_num [half])

/-- Almost-sure termination contract for the declared finite-prefix semantics. -/
theorem nontermination_mass_tendsto_zero (q : ℕ) (hq : 0 < q) (r : Fin q) :
    Tendsto (fun t => (fuelLaw q hq r t).mass none) atTop (𝓝 0) := by
  simpa only [fuel_wait_mass] using half_pow_tendsto_zero

theorem fuel_true_tendsto (q : ℕ) (hq : 0 < q) (r : Fin q) :
    Tendsto (fun t => (fuelLaw q hq r t).mass (some true)) atTop (𝓝 (fraction q r)) := by
  have hz : Tendsto (fun t => half^t * fraction q (remainder q hq r t)) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro t
      exact mul_nonneg (pow_nonneg (by norm_num [half]) t) (fraction_nonneg q hq _)
    · intro t
      exact mul_le_of_le_one_right (pow_nonneg (by norm_num [half]) t)
        (fraction_lt_one q hq _).le
    · exact half_pow_tendsto_zero
  have hl : Tendsto
      (fun t => fraction q r - half^t * fraction q (remainder q hq r t))
      atTop (𝓝 (fraction q r - 0)) := tendsto_const_nhds.sub hz
  simpa only [fuel_true_formula, sub_zero] using hl

/-- Probability of the unique halting bit word at depth t+1. -/
def terminalWeight (t : ℕ) : ℝ := half^(t+1)

theorem first_halt_mass (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ) :
    (fuelLaw q hq r t).mass none - (fuelLaw q hq r (t+1)).mass none =
      terminalWeight t := by
  rw [fuel_wait_mass, fuel_wait_mass]
  simp only [terminalWeight, pow_succ, half]
  ring

theorem finite_true_sum (q : ℕ) (hq : 0 < q) (r : Fin q) (t : ℕ) :
    (fuelLaw q hq r t).mass (some true) =
      ∑ k ∈ range t, if outputAt q hq r k then terminalWeight k else 0 := by
  induction t generalizing r with
  | zero => simp [fuelLaw, Law.pure]
  | succ t ih =>
    rw [fuel_true_succ, ih, Finset.sum_range_succ']
    simp only [outputAt, remainder, terminalWeight, pow_one]
    rw [Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    cases hd : digit q (remainder q hq (nextRemainder q hq r) k) <;>
      simp [hd, pow_succ] <;> ring

theorem halting_trace_mass_one : HasSum terminalWeight 1 := by
  simpa [terminalWeight, pow_succ, half] using hasSum_geometric_two.mul_right (1/2:ℝ)

/-- Exact random-bit/read cost, including the final mismatching bit. Not arithmetic cost. -/
theorem expected_fair_bits_two :
    HasSum (fun t : ℕ => (t+1:ℕ) * terminalWeight t) (2:ℝ) := by
  have hw : HasSum (fun t : ℕ => (t:ℝ)*half^t) 2 := by
    simpa [half] using
      (hasSum_coe_mul_geometric_of_norm_lt_one (r:=(1/2:ℝ)) (by norm_num))
  have hg : HasSum (fun t : ℕ => half^t) 2 := by simpa [half] using hasSum_geometric_two
  convert (hw.add hg).mul_right half using 1
  · funext t
    simp only [terminalWeight, pow_succ, Nat.cast_add, Nat.cast_one]
    ring
  · norm_num [half]

theorem true_trace_mass (q : ℕ) (hq : 0 < q) (r : Fin q) :
    HasSum (fun t => if outputAt q hq r t then terminalWeight t else 0) (fraction q r) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun t => by
      split_ifs
      · exact pow_nonneg (by norm_num [half]) _
      · exact le_rfl) (fraction q r)).mpr
  simpa only [←finite_true_sum] using fuel_true_tendsto q hq r

/-- Derived terminal output law; this is not a primitive draw or an input assumption. -/
noncomputable def outputLaw (q : ℕ) (hq : 0 < q) (r : Fin q) : Law Bool where
  mass b := if b then fraction q r else 1-fraction q r
  nonneg b := by
    cases b <;> simp <;> linarith [fraction_nonneg q hq r, fraction_lt_one q hq r]
  total := by simp <;> ring

theorem outputLaw_execution_mass (q : ℕ) (hq : 0 < q) (r : Fin q) (b : Bool) :
    HasSum (fun t => if outputAt q hq r t = b then terminalWeight t else 0)
      ((outputLaw q hq r).mass b) := by
  cases b with
  | true => simpa [outputLaw] using true_trace_mass q hq r
  | false =>
    have h := halting_trace_mass_one.sub (true_trace_mass q hq r)
    have he : (fun t => terminalWeight t -
        (if outputAt q hq r t then terminalWeight t else 0)) =
        (fun t => if outputAt q hq r t = false then terminalWeight t else 0) := by
      funext t
      cases outputAt q hq r t <;> simp
    simpa only [he, outputLaw, Bool.false_eq_true, if_false] using h

def initial (f : ℕ) (hf : 0 < f) : Fin (2*f) := ⟨1, by omega⟩

theorem initial_fraction (f : ℕ) (hf : 0 < f) :
    fraction (2*f) (initial f hf) = 1/(2*(f:ℝ)) := by
  simp [fraction, initial, Nat.cast_mul]

theorem sampler_exact_bias (f : ℕ) (hf : 0 < f) :
    HasSum (fun t => if outputAt (2*f) (by omega) (initial f hf) t
      then terminalWeight t else 0) (1/(2*(f:ℝ))) := by
  simpa only [initial_fraction] using true_trace_mass (2*f) (by omega) (initial f hf)

end LightEFTSpanners.FairBitDigit
