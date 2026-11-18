import DirectedFlowCutGap.EncodedVertexInput
import DirectedFlowCutGap.EncodedAmplification

/-!
# Amplified rational vertex solver

Independent solver draws are compared by the rational price of their
actual output cuts. One additional parameter controls the accumulated
fair-bit rejection error across the entire repeated execution.
-/

namespace DirectedFlowCutGap.EncodedVertexAmplification

open scoped NNReal
open EncodedVertexSolver FiniteDrawTrees FiniteAmplification
open RawNonnegativeRational

attribute [local instance] EncodedUniformRounding.flagsFintype

private def key {n : ℕ} : Output n → Option (FractionalCoverRawGraph.Pair n) ⊕ RetainedGridState.Flags n
  | .infeasible d => .inl (some d)
  | .invalid => .inl none
  | .cut mask => .inr mask

private theorem key_injective (n : ℕ) : Function.Injective (@key n) := by
  intro a b h
  cases a <;> cases b <;> simp_all [key]

local instance (n : ℕ) : Finite (Output n) := Finite.of_injective key (key_injective n)

noncomputable local instance (n : ℕ) : Fintype (Output n) := Fintype.ofFinite _

def codePrice {n : ℕ} (D : GraphInput n) : Output n → Code
  | .cut mask => EncodedCutSelection.maskCost D.costs mask
  | .invalid | .infeasible _ => Code.zero

theorem codePrice_value {n : ℕ} (D : GraphInput n) (out : Output n) :
    ((codePrice D out).realValue : ℝ) = outputPrice D out := by
  cases out with
  | cut mask =>
    change ((EncodedCutSelection.maskCost D.costs mask).realValue : ℝ) =
      ((cutCost (fun i => (FractionalCoverRawCore.get D.costs i).realValue)
        (EncodedUnitCostReplication.selectedSet mask) : ℝ≥0) : ℝ)
    rw [EncodedCutSelection.maskCost_value]
  | infeasible _ | invalid =>
    simp [codePrice, outputPrice, outputMask, EncodedCutSelection.optionPrice, Code.realValue]

def roundDrawBound (n : ℕ) : ℕ := EncodedUniformRounding.drawBound (4 * n ^ 2)

def bitTree {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n) (round : Rounding n) :
    FiniteDrawTrees.Tree (Output n) :=
  EncodedAmplification.bitTree (codePrice D) (tree D round)
    (drawBound D (roundDrawBound n)) extraSamples confidence

def massBitTree {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n) :
    FiniteDrawTrees.Tree (Output n) :=
  bitTree extraSamples confidence D EncodedWeightedRounding.tree

def sizeBitTree {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n) :
    FiniteDrawTrees.Tree (Output n) :=
  bitTree extraSamples confidence D EncodedSizeRounding.tree

theorem bitTree_binary {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n) (round : Rounding n) :
    LazyFairBitTrees.Binary (bitTree extraSamples confidence D round) :=
  EncodedAmplification.bitTree_binary ..

theorem massBit_support_valid {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n) {out : Output n}
    (hout : out ∈ (ideal (massBitTree extraSamples confidence D)).support) : Valid D out := by
  have h := EncodedAmplification.support_selected (codePrice D) (tree D EncodedWeightedRounding.tree)
    (drawBound D (roundDrawBound n)) extraSamples confidence hout
  exact support_valid D EncodedWeightedRounding.tree
    (fun r _ hr => EncodedWeightedRounding.support_valid r hr) h

theorem sizeBit_support_valid {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n) {out : Output n}
    (hout : out ∈ (ideal (sizeBitTree extraSamples confidence D)).support) : Valid D out := by
  have h := EncodedAmplification.support_selected (codePrice D) (tree D EncodedSizeRounding.tree)
    (drawBound D (roundDrawBound n)) extraSamples confidence hout
  exact support_valid D EncodedSizeRounding.tree
    (fun r _ hr => EncodedSizeRounding.support_valid r hr) h

theorem failure_le {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n) (round : Rounding n)
    (hround : ∀ r : RoundingInput n, Within (roundDrawBound n) (round r))
    (B : ℝ) (hB : 0 < B) (hcost : expectedPrice D round ≤ B) :
    probability (ideal (bitTree extraSamples confidence D round))
      (fun out => 2 * B < outputPrice D out) ≤
      ((1 : ℝ) / 2) ^ (extraSamples + 1) + ((1 : ℝ) / 2) ^ confidence := by
  have hb := EncodedAmplification.failure_le (codePrice D) (tree D round)
    (drawBound D (roundDrawBound n)) extraSamples confidence
    (tree_within D round (roundDrawBound n) hround) B hB
  simp only [codePrice_value] at hb
  apply hb
  rw [expectedPrice, expectedCost_map] at hcost
  exact hcost

theorem massBit_failure_le {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n)
    (B : ℝ) (hB : 0 < B) (hcost : expectedPrice D EncodedWeightedRounding.tree ≤ B) :
    probability (ideal (massBitTree extraSamples confidence D))
      (fun out => 2 * B < outputPrice D out) ≤
      ((1 : ℝ) / 2) ^ (extraSamples + 1) + ((1 : ℝ) / 2) ^ confidence :=
  failure_le extraSamples confidence D _ EncodedWeightedRounding.tree_within B hB hcost

theorem sizeBit_failure_le {n : ℕ} (extraSamples confidence : ℕ) (D : GraphInput n)
    (B : ℝ) (hB : 0 < B) (hcost : expectedPrice D EncodedSizeRounding.tree ≤ B) :
    probability (ideal (sizeBitTree extraSamples confidence D))
      (fun out => 2 * B < outputPrice D out) ≤
      ((1 : ℝ) / 2) ^ (extraSamples + 1) + ((1 : ℝ) / 2) ^ confidence :=
  failure_le extraSamples confidence D _ EncodedSizeRounding.tree_within B hB hcost

def confidenceExponent (n κ : ℕ) : ℕ := FairBitWords.width (max 1 n) * κ

def polynomialBitTree {n : ℕ} (κ : ℕ) (D : GraphInput n) (round : Rounding n) :
    FiniteDrawTrees.Tree (Output n) :=
  let e := confidenceExponent n κ
  bitTree e (e + 1) D round

private theorem confidence_power (n κ : ℕ) :
    ((1 : ℝ) / 2) ^ (confidenceExponent n κ) ≤
      ((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ)) := by
  let m := max 1 n
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_one.trans_le (le_max_left 1 n))
  have hM : (m : ℝ) ≤ 2 ^ FairBitWords.width m := by
    exact_mod_cast (FairBitWords.lt_bucket m).le
  change ((1 : ℝ) / 2) ^ (FairBitWords.width m * κ) ≤ (m : ℝ) ^ (-(κ : ℝ))
  rw [div_pow, one_pow, pow_mul, Real.rpow_neg hm.le, Real.rpow_natCast, ← one_div]
  exact one_div_le_one_div_of_le (pow_pos hm _) (pow_le_pow_left₀ hm.le hM _)

theorem polynomial_failure_le {n : ℕ} (κ : ℕ) (D : GraphInput n) (round : Rounding n)
    (hround : ∀ r : RoundingInput n, Within (roundDrawBound n) (round r))
    (B : ℝ) (hB : 0 < B) (hcost : expectedPrice D round ≤ B) :
    probability (ideal (polynomialBitTree κ D round))
      (fun out => 2 * B < outputPrice D out) ≤ ((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ)) := by
  let e := confidenceExponent n κ
  calc
    _ ≤ ((1 : ℝ) / 2) ^ (e + 1) + ((1 : ℝ) / 2) ^ (e + 1) :=
      failure_le e (e + 1) D round hround B hB hcost
    _ = ((1 : ℝ) / 2) ^ e := by rw [pow_succ]; ring
    _ ≤ _ := confidence_power n κ

/-- Decode the existing wire format, then run the amplified solver in the chosen mode. -/
def sourcePolynomialBitTree (κ : ℕ) (round : (n : ℕ) → Rounding n)
    (source : BinaryArithmetic.Bits) :
    Option (Σ n, FiniteDrawTrees.Tree (Output n)) :=
  (EncodedVertexInput.parse source).map fun ⟨n, D⟩ =>
    ⟨n, polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (round n)⟩

theorem sourcePolynomialBitTree_encode (κ : ℕ) (round : (n : ℕ) → Rounding n)
    {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    sourcePolynomialBitTree κ round (SourcePacking.encode D.costs D.adjacency D.demands) =
      some ⟨n, polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (round n)⟩ := by
  simp [sourcePolynomialBitTree, EncodedVertexInput.parse_encode]

end DirectedFlowCutGap.EncodedVertexAmplification
