import DirectedFlowCutGap.EncodedBinarySampling
import DirectedFlowCutGap.BinaryFractionalRows
import DirectedFlowCutGap.BinaryArrayBatch
import DirectedFlowCutGap.BinaryVectorAccess
import DirectedFlowCutGap.BinaryNaturalOperations

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

private def fieldWithControl {n : ℕ} (costs : Row n) (mask : Flags n) (i : Fin n) :
    (Fraction × ℕ) × ℕ :=
  let keep := BinaryVectorAccess.read mask i
  if keep.1 then
    let price := BinaryVectorAccess.read costs i
    ((price.1,0),keep.2+price.2+4)
  else ((zero,0),keep.2+4)

private theorem field_value {n : ℕ} (costs : Row n) (mask : Flags n) (i : Fin n) :
    (fieldWithControl costs mask i).1=((if mask[i.val] then get costs i else zero),0) := by
  simp only [fieldWithControl,BinaryVectorAccess.read_value,BinaryFractionalRows.get]
  split <;> rfl

private theorem field_paid {n : ℕ} (costs : Row n) (mask : Flags n) (i : Fin n) :
    (fieldWithControl costs mask i).2≤2*BinaryVectorAccess.budget n+4 := by
  have keep := BinaryVectorAccess.read_paid mask i (BinaryNaturalOperations.size_le_self n)
  have val := BinaryVectorAccess.read_paid costs i (BinaryNaturalOperations.size_le_self n)
  unfold fieldWithControl
  dsimp only
  split <;> omega

def maskFieldsWithControl {n : ℕ} (costs : Row n) (mask : Flags n) : List Fraction × ℕ :=
  let stored := BinaryArrayBatch.runWithChildWork (fieldWithControl costs mask)
  (stored.1.1.toList,stored.1.2+stored.2+2*n+4)

theorem maskFields_value {n : ℕ} (costs : Row n) (mask : Flags n) :
    (maskFieldsWithControl costs mask).1=fields costs mask := by
  simp only [maskFieldsWithControl,BinaryArrayBatch.runWithChildWork_value,field_value,
    Vector.toList_ofFn,fields]

def fieldControlBudget {R : Type*} [Semiring R] (n : R) : R :=
  8*n+4+BinaryArrayBatch.childCeiling n 0 (2*BinaryVectorAccess.budget n+4)+2*n+4

theorem fieldControlBudget_mono {n m : ℕ} (size : n ≤ m) :
    fieldControlBudget n ≤ fieldControlBudget m := by
  unfold fieldControlBudget BinaryArrayBatch.childCeiling BinaryVectorAccess.budget
  gcongr

theorem maskFields_paid {n : ℕ} (costs : Row n) (mask : Flags n) :
    (maskFieldsWithControl costs mask).2≤fieldControlBudget n := by
  have paid := BinaryArrayBatch.runWithChildWork_paid (fieldWithControl costs mask)
    (cap := 0) (fun i => by simp only [field_value,le_refl]) (field_paid costs mask)
  let batch := BinaryArrayBatch.runWithChildWork (fieldWithControl costs mask)
  have stored : batch.1.2=8*n+4 := by
    simp only [batch,BinaryArrayBatch.runWithChildWork_value,field_value,List.map_ofFn,Function.comp_def,
      List.ofFn_const,List.sum_replicate,nsmul_zero,Nat.zero_add]
  change batch.1.2+batch.2+2*n+4≤fieldControlBudget n
  rw [stored]
  unfold fieldControlBudget
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (paid.trans (BinaryArrayBatch.childBudget_le _ _ _)) _) _) _

/-- Read the reached mask and price slots once before totaling a cut. -/
def cutScoreWithControl {n : ℕ} (costs : Row n) (out : EncodedVertexSolver.Output n) :
    (Fraction × ℕ) × ℕ :=
  match out with
  | .cut mask =>
    let data := maskFieldsWithControl costs mask
    (sum data.1,data.2)
  | .invalid | .infeasible _ => ((zero,0),0)

theorem cutScore_control_value {n : ℕ} (costs : Row n) (out : EncodedVertexSolver.Output n) :
    (cutScoreWithControl costs out).1=cutScore costs out := by
  cases out <;> simp only [cutScoreWithControl,cutScore,maskScore,maskFields_value]

theorem cutScore_control_paid {n : ℕ} (costs : Row n) (out : EncodedVertexSolver.Output n) :
    (cutScoreWithControl costs out).2≤fieldControlBudget n := by
  cases out
  · exact Nat.zero_le _
  · apply maskFields_paid
  · exact Nat.zero_le _

def minimumLast {A : Type} (score : A → (Fraction × ℕ) × ℕ) (value : A) : Choice A × ℕ :=
  let price := score value
  (⟨value,price.1.1,price.1.2⟩,price.2+2)

def minimumPrepend {A : Type} (score : A → (Fraction × ℕ) × ℕ) (value : A) (tail : Choice A × ℕ) :
    Choice A × ℕ :=
  let head := score value
  let comp := BinaryRational.le head.1.1 tail.1.price
  let fees := CachedScalarRead.sumMeasured [head.1.2,tail.1.charge,comp.2]
  let chosen : Choice A := if comp.1 then ⟨value,head.1.1,fees.1⟩ else ⟨tail.1.value,tail.1.price,fees.1⟩
  (chosen,head.2+tail.2+fees.2+8)

/-- Choose the same minimum, counting reached price reads and the binary
addition of the existing fees. Ties keep the first cut. -/
def minimumWithControl {A : Type} (score : A → (Fraction × ℕ) × ℕ) :
    (n : ℕ) → (Fin (n+1) → A) → Choice A × ℕ
  | 0, samples => minimumLast score (samples 0)
  | n+1, samples => minimumPrepend score (samples 0) (minimumWithControl score n (Fin.tail samples))

theorem minimumWithControl_value {A : Type} (score : A → (Fraction × ℕ) × ℕ) (n : ℕ)
    (samples : Fin (n+1) → A) :
    (minimumWithControl score n samples).1=minimum (fun a => (score a).1) n samples := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [minimumWithControl,minimumPrepend,minimum,ih,CachedScalarRead.sum_value,List.sum_cons,List.sum_nil,
      Nat.add_zero,Nat.add_assoc]

def minimumControlBudget {R : Type*} [Semiring R] (n childCap B : R) : R :=
  (n+1)*(childCap+3*(96*(B+2)^2+4)+9)

theorem minimumControlBudget_mono {n m c C b B : ℕ} (cycles : n ≤ m) (children : c ≤ C) (width : b ≤ B) :
    minimumControlBudget n c b ≤ minimumControlBudget m C B := by
  unfold minimumControlBudget
  gcongr

theorem minimumWithControl_paid {A : Type} (score : A → (Fraction × ℕ) × ℕ)
    (n : ℕ) (samples : Fin (n+1) → A) {childCap B : ℕ}
    (each : ∀ a, (score a).2 ≤ childCap)
    (width : (minimum (fun a => (score a).1) n samples).charge.size≤B) :
    (minimumWithControl score n samples).2 ≤ minimumControlBudget n childCap B := by
  induction n with
  | zero =>
    have head := each (samples 0)
    simp only [minimumWithControl,minimumLast,minimumControlBudget,Nat.zero_add,Nat.one_mul]
    omega
  | succ n ih =>
    let head := score (samples 0)
    let tail := minimumWithControl score n (Fin.tail samples)
    let comp := BinaryRational.le head.1.1 tail.1.price
    let fees : List ℕ := [head.1.2,tail.1.charge,comp.2]
    have earlier : tail.1=minimum (fun a => (score a).1) n (Fin.tail samples) :=
      minimumWithControl_value score n (Fin.tail samples)
    have total : fees.sum=(minimum (fun a => (score a).1) (n+1) samples).charge := by
      simp only [fees,minimum,head,comp,earlier,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
      split <;> rfl
    have bounded : fees.sum.size≤B := by rw [total]; exact width
    have tailWidth : (minimum (fun a => (score a).1) n (Fin.tail samples)).charge.size≤B := by
      rw [← earlier]
      apply (Nat.size_le_size ?_).trans bounded
      simp only [fees,List.sum_cons,List.sum_nil,Nat.add_zero]
      omega
    have more : tail.2 ≤ minimumControlBudget n childCap B := ih (Fin.tail samples) tailWidth
    have sum : (CachedScalarRead.sumMeasured fees).2≤3*(96*(B+2)^2+4)+1 := by
      simpa only [fees,List.length_cons,List.length_nil] using CachedScalarRead.sum_paid fees bounded
    have headPaid : head.2≤childCap := each (samples 0)
    change head.2+tail.2+(CachedScalarRead.sumMeasured fees).2+8≤_
    unfold minimumControlBudget at more ⊢
    rw [Nat.add_mul,Nat.one_mul]
    omega

open Polynomial in
theorem fieldControlBudget_eval (n : Polynomial ℕ) (x : ℕ) :
    (fieldControlBudget n).eval x=fieldControlBudget (n.eval x) := by
  simp only [fieldControlBudget,BinaryArrayBatch.childCeiling,BinaryVectorAccess.budget,
    eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_zero]

open Polynomial in
theorem minimumControlBudget_eval (n childCap B : Polynomial ℕ) (x : ℕ) :
    (minimumControlBudget n childCap B).eval x=
      minimumControlBudget (n.eval x) (childCap.eval x) (B.eval x) := by
  simp only [minimumControlBudget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

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
