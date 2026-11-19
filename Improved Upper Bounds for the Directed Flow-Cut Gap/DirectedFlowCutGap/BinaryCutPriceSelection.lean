import DirectedFlowCutGap.EncodedBinarySampling
import DirectedFlowCutGap.BinaryFractionalRows

/-!
# Binary rational arithmetic for comparing repeated cuts

Compute each input cut's price once. Retain the winner and its encoded
price, including the original tie order of the amplified solver. The
charge counts the binary rational additions and comparisons.
-/

namespace DirectedFlowCutGap.BinaryCutPriceSelection

open BinaryRational BinaryFractionalRows
open RetainedGridState (Flags)
open RawNonnegativeRational

structure Choice (A : Type) where
  value : A
  price : Fraction
  charge : ℕ

def minimum {A : Type} (score : A → Fraction × ℕ) : (n : ℕ) → (Fin (n + 1) → A) → Choice A
  | 0, samples =>
    let price := score (samples 0)
    ⟨samples 0, price.1, price.2⟩
  | n + 1, samples =>
    let tail := minimum score n (Fin.tail samples)
    let head := score (samples 0)
    let compare := BinaryRational.le head.1 tail.price
    let charge := head.2 + tail.charge + compare.2
    if compare.1 then ⟨samples 0, head.1, charge⟩ else ⟨tail.value, tail.price, charge⟩

theorem minimum_refines {A : Type} (score : A → Fraction × ℕ) (price : A → Code)
    (hprice : ∀ a, decode (score a).1 = price a) (n : ℕ) (samples : Fin (n + 1) → A) :
    (minimum score n samples).value = EncodedAmplification.minimum price n samples ∧
      decode (minimum score n samples).price = price (minimum score n samples).value := by
  induction n with
  | zero => exact ⟨rfl, hprice (samples 0)⟩
  | succ n ih =>
    obtain ⟨hv, hp⟩ := ih (Fin.tail samples)
    simp only [minimum, EncodedAmplification.minimum, EncodedAmplification.cheaper, le_decode, hprice, hp, ← hv]
    split <;> simp only [hprice, hp, and_self]

theorem minimum_charge {A : Type} (score : A → Fraction × ℕ) (n : ℕ) (samples : Fin (n + 1) → A)
    (B C : ℕ) (hscore : ∀ i, StoredBounded (score (samples i)).1 B ∧ (score (samples i)).2 ≤ C) :
    StoredBounded (minimum score n samples).price B ∧
      (minimum score n samples).charge ≤ (n + 1) * C + n * (2048 * (B + 1)^2) := by
  induction n with
  | zero => simpa only [minimum, Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.add_zero] using hscore 0
  | succ n ih =>
    obtain ⟨htw, htc⟩ := ih (Fin.tail samples) (fun i => hscore i.succ)
    obtain ⟨hhw, hhc⟩ := hscore 0
    have hc := le_charge hhw htw
    have htotal := Nat.add_le_add (Nat.add_le_add hhc htc) hc
    have he : C + ((n + 1) * C + n * (2048 * (B + 1)^2)) + 2048 * (B + 1)^2 =
      (n + 1 + 1) * C + (n + 1) * (2048 * (B + 1)^2) := by ring
    rw [he] at htotal
    unfold minimum
    dsimp only
    split
    · exact ⟨hhw, htotal⟩
    · exact ⟨htw, htotal⟩

def fields {n : ℕ} (costs : Row n) (mask : Flags n) : List Fraction :=
  List.ofFn fun i : Fin n => if mask[i.val] then get costs i else zero

def maskScore {n : ℕ} (costs : Row n) (mask : Flags n) : Fraction × ℕ := sum (fields costs mask)

theorem maskScore_decodes {n : ℕ} (costs : Row n) (mask : Flags n) :
    decode (maskScore costs mask).1 = EncodedCutSelection.maskCost (decodeRow costs) mask := by
  rw [maskScore, sum_decode, EncodedCutSelection.maskCost]
  unfold fields
  rw [List.map_ofFn]
  apply congrArg (fun f : Fin n → Code => FractionalCoverRawCore.sumCodes (List.ofFn f))
  funext i
  simp only [Function.comp_apply, decode_get]
  split <;> rfl

theorem maskScore_charge {n : ℕ} (costs : Row n) (mask : Flags n) {B : ℕ} (hB : 1 ≤ B)
    (hc : ∀ i, StoredBounded (get costs i) B) :
    StoredBounded (maskScore costs mask).1 (n * (B + 1) + 1) ∧
      (maskScore costs mask).2 ≤ sumBound n B := by
  have hfield : ∀ a ∈ fields costs mask, StoredBounded a B := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    split
    · exact hc i
    · exact ⟨by simp [zero], by simpa [zero] using hB⟩
  have hlen : (fields costs mask).length = n := by simp [fields]
  refine ⟨?_, ?_⟩
  · simpa only [maskScore, hlen] using sum_stored_bound (fields costs mask) B
      (fun a ha => stored_raw_bound (hfield a ha))
  · simpa only [maskScore, hlen] using sum_charge (fields costs mask) B hfield

def cutScore {n : ℕ} (costs : Row n) : EncodedVertexSolver.Output n → Fraction × ℕ
  | .cut mask => maskScore costs mask
  | .invalid | .infeasible _ => (zero, 0)

theorem cutScore_decodes {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (a : EncodedVertexSolver.Output n) :
    decode (cutScore D.costs a).1 = EncodedVertexAmplification.codePrice (BinaryFractionalGuesses.decodeInput D) a := by
  cases a
  · rfl
  · exact maskScore_decodes _ _
  · rfl

theorem cutScore_charge {n : ℕ} (costs : Row n) (a : EncodedVertexSolver.Output n)
    {B : ℕ} (hB : 1 ≤ B) (hc : ∀ i, StoredBounded (get costs i) B) :
    StoredBounded (cutScore costs a).1 (n * (B + 1) + 1) ∧ (cutScore costs a).2 ≤ sumBound n B := by
  cases a
  · exact ⟨⟨by simp [cutScore, zero], by simp [cutScore, zero]⟩, Nat.zero_le _⟩
  · exact maskScore_charge costs _ hB hc
  · exact ⟨⟨by simp [cutScore, zero], by simp [cutScore, zero]⟩, Nat.zero_le _⟩

open FiniteDrawTrees LazyFairBitTrees
open BinaryDrawTreeExecution (DrawTree)

def pricedSamples {n : ℕ} (costs : Row n) (t : DrawTree (EncodedVertexSolver.Output n)) (extra : ℕ) :
    DrawTree (EncodedVertexSolver.Output n × ℕ) :=
  map (fun samples =>
    let result := minimum (cutScore costs) extra samples
    (result.value, result.charge)) (EncodedAmplification.samples t (extra + 1))

theorem pricedSamples_value {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (t : DrawTree (EncodedVertexSolver.Output n)) (extra : ℕ) :
    Prod.fst <$> pricedSamples D.costs t extra =
      EncodedAmplification.selectedTree (EncodedVertexAmplification.codePrice (BinaryFractionalGuesses.decodeInput D)) t extra := by
  unfold pricedSamples EncodedAmplification.selectedTree
  change Prod.fst <$> (_ <$> _) = _ <$> _
  rw [Functor.map_map]
  congr 1
  funext samples
  exact (minimum_refines (cutScore D.costs) _ (cutScore_decodes D) extra samples).1

def selectionBound (extra n B : ℕ) : ℕ :=
  (extra + 1) * sumBound n B + extra * (2048 * (n * (B + 1) + 2)^2)

theorem pricedSamples_charge {n B extra : ℕ} (costs : Row n) (t : DrawTree (EncodedVertexSolver.Output n))
    (hB : 1 ≤ B) (hc : ∀ i, StoredBounded (get costs i) B)
    {out : EncodedVertexSolver.Output n × ℕ} (ho : out ∈ (ideal (pricedSamples costs t extra)).support) :
    out.2 ≤ selectionBound extra n B := by
  unfold pricedSamples ideal at ho
  rw [law_map] at ho
  obtain ⟨xs, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  have h := minimum_charge (cutScore costs) extra xs (n * (B + 1) + 1) (sumBound n B)
    (fun i => cutScore_charge costs (xs i) hB hc)
  exact h.2

private theorem lower_value_map {A C : Type} (T : ℕ) (f : A → C) (t : DrawTree A) :
    f <$> lower T t = lower T (f <$> t) := by
  induction t with
  | pure a => rfl
  | draw n hn next ih =>
    change f <$> (rejection n hn T >>= fun r => lower T (next r.value)) =
      rejection n hn T >>= fun r => lower T (f <$> next r.value)
    simp only [map_bind, ih]

def amplified {n : ℕ} (costs : Row n) (t : DrawTree (EncodedVertexSolver.Output n))
    (Q extra confidence : ℕ) : DrawTree ((EncodedVertexSolver.Output n × ℕ) × ℕ) :=
  BinaryDrawTreeExecution.run (FairBitConfidence.trials ((extra + 1) * Q) confidence) (pricedSamples costs t extra)

theorem amplified_value {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (t : DrawTree (EncodedVertexSolver.Output n)) (Q extra confidence : ℕ) :
    (fun a => a.1.1) <$> amplified D.costs t Q extra confidence =
      EncodedAmplification.bitTree (EncodedVertexAmplification.codePrice (BinaryFractionalGuesses.decodeInput D))
        t Q extra confidence := by
  calc
    _ = Prod.fst <$> (Prod.fst <$> amplified D.costs t Q extra confidence) := by simp only [Functor.map_map]
    _ = _ := by
      rw [amplified, BinaryDrawTreeExecution.run_value, lower_value_map, pricedSamples_value]
      rfl

theorem amplified_selection_charge {n B Q extra confidence : ℕ} (costs : Row n)
    (t : DrawTree (EncodedVertexSolver.Output n)) (hB : 1 ≤ B) (hc : ∀ i, StoredBounded (get costs i) B)
    {out : (EncodedVertexSolver.Output n × ℕ) × ℕ}
    (ho : out ∈ (ideal (amplified costs t Q extra confidence)).support) :
    out.1.2 ≤ selectionBound extra n B := by
  let T := FairBitConfidence.trials ((extra + 1) * Q) confidence
  let samples := pricedSamples costs t extra
  have hs : out.1 ∈ (ideal (lower T samples)).support := by
    rw [← BinaryDrawTreeExecution.run_value]
    change out.1 ∈ (law uniformDraw (map Prod.fst (BinaryDrawTreeExecution.run T samples))).support
    rw [law_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, ho, rfl⟩
  exact pricedSamples_charge costs t hB hc (lowered_support_subset_ideal T samples hs)

end DirectedFlowCutGap.BinaryCutPriceSelection
