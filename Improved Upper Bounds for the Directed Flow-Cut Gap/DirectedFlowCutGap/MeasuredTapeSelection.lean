import DirectedFlowCutGap.PaidVertexAmplification

/-! Measure the terminal score calculation on the very same amplified
tape. A failed tape never reaches the terminal selection. -/
namespace DirectedFlowCutGap.MeasuredTapeSelection

open BinaryRational (Fraction StoredBounded)
open RawNonnegativeRational (Code)
open BinaryArithmetic (Bits)
open PhysicalCoverAccess (Read)

private def encoded {A : Type} (score : A → Code × ℕ) (a : A) : Fraction × ℕ :=
  let cost := score a
  let packed := BinaryRawRational.encode cost.1
  (packed.1,cost.2+packed.2)

def select {A : Type} (score : A → Code × ℕ) : (extra : ℕ) → (Fin (extra+1) → A) → A × ℕ
  | 0, xs => (xs 0,0)
  | extra+1, xs =>
    let chosen := BinaryCutPriceSelection.minimumWithControl (fun a => (encoded score a,0)) (extra+1) xs
    (chosen.1.value,chosen.1.charge+chosen.2)

theorem select_value {A : Type} (score : A → Code × ℕ) (plain : A → Code)
    (value : ∀ a, (score a).1 = plain a) (extra : ℕ) (xs : Fin (extra+1) → A) :
    (select score extra xs).1 = EncodedAmplification.minimum plain extra xs := by
  cases extra with
  | zero => rfl
  | succ extra =>
    simp only [select,BinaryCutPriceSelection.minimumWithControl_value]
    exact (BinaryCutPriceSelection.minimum_refines (encoded score) plain
      (fun a => by simp only [encoded,BinaryRawRational.encode_value,value]) (extra+1) xs).1

private def comparisons (extra B C : ℕ) : ℕ :=
  (extra+1)*(C+40*(B+2)^2)+extra*(2048*(B+2)^2)

def work (extra B C : ℕ) : ℕ :=
  let paid := comparisons extra B C
  paid+BinaryCutPriceSelection.minimumControlBudget extra 0 paid.size

theorem select_charge {A : Type} (score : A → Code × ℕ) (extra : ℕ)
    (xs : Fin (extra+1) → A) {B C : ℕ} (fits : ∀ i, (score (xs i)).1.Bounded B ∧ (score (xs i)).2 ≤ C) :
    (select score extra xs).2 ≤ work extra B C := by
  cases extra with
  | zero => exact Nat.zero_le _
  | succ extra =>
    have arithmetic : (BinaryCutPriceSelection.minimum (encoded score) (extra+1) xs).charge ≤
        comparisons (extra+1) B C := by
      refine (BinaryCutPriceSelection.minimum_charge (encoded score) (extra+1) xs (B+1) (C+40*(B+2)^2) ?_).2
      intro i
      obtain ⟨width,charged⟩ := fits i
      exact ⟨BinaryRawRational.encode_width width,Nat.add_le_add charged (BinaryRawRational.encode_paid width)⟩
    have control := BinaryCutPriceSelection.minimumWithControl_paid (fun a => (encoded score a,0))
      (extra+1) xs (childCap:=0) (fun _ => Nat.le_refl 0) (Nat.size_le_size arithmetic)
    simpa only [select,work,BinaryCutPriceSelection.minimumWithControl_value] using Nat.add_le_add arithmetic control

def sampleWork (count budget : ℕ) : ℕ :=
  let paid := count*(budget+4)+1
  paid+(count*PaidVertexAmplification.sampleControlBudget (paid+4).size+1)

def run {A : Type} (one : Bits → Read ((A × ℕ) × Bits)) (score : A → Code × ℕ)
    (extra : ℕ) (bits : Bits) : Read (A × Bits) :=
  let attempts := PaidVertexAmplification.samplesWithCharges one (extra+1) bits
  match attempts.1.1 with
  | none => (none,attempts.1.2+attempts.2)
  | some (xs,rest) =>
    let winner := select score extra (fun i => (xs i).1)
    (some (winner.1,rest),attempts.1.2+attempts.2+winner.2)

theorem run_value {A : Type} (one : Bits → Read ((A × ℕ) × Bits))
    (score : A → Code × ℕ) (plain : A → Code) (value : ∀ a, (score a).1 = plain a)
    (t : FiniteDrawTrees.Tree A) (trials extra : ℕ)
    (observes : ∀ bits, (one bits).1.map (fun ((a,_),tail) => (a,tail)) =
      LiteralTapeComposition.execute trials t bits) (bits : Bits) :
    (run one score extra bits).1 =
      LiteralTapeComposition.execute trials (EncodedAmplification.selectedTree plain t extra) bits := by
  have samples := PhysicalAmplifiedVertexSolver.samples_observe (fun tape => (one tape).1)
    trials (extra+1) t observes bits
  rw [← PaidVertexAmplification.samples_value one (extra+1) bits] at samples
  unfold EncodedAmplification.selectedTree
  rw [LiteralTapeComposition.execute_map,← samples]
  cases found : (PaidVertexAmplification.samples one (extra+1) bits).1 with
  | none => simp only [run,PaidVertexAmplification.samplesWithCharges_reference,found,Option.map_none]
  | some result =>
    rcases result with ⟨cuts,rest⟩
    simp only [run,PaidVertexAmplification.samplesWithCharges_reference,found,Option.map_some,select_value score plain value]

theorem run_charge {A : Type} (one : Bits → Read ((A × ℕ) × Bits)) (score : A → Code × ℕ)
    (extra : ℕ) (bits : Bits) {B C budget : ℕ} (onePaid : ∀ bits, (one bits).2 ≤ budget)
    (fits : ∀ a, (score a).1.Bounded B ∧ (score a).2 ≤ C) :
    (run one score extra bits).2 ≤ sampleWork (extra+1) budget+work extra B C := by
  have attempted := PaidVertexAmplification.samples_paid one budget (extra+1) onePaid bits
  have control := PaidVertexAmplification.samplesWithCharges_paid one (extra+1) bits
    (Nat.size_le_size (Nat.add_le_add_right attempted 4))
  have sampling : (PaidVertexAmplification.samples one (extra+1) bits).2+
      (PaidVertexAmplification.samplesWithCharges one (extra+1) bits).2 ≤ sampleWork (extra+1) budget :=
    Nat.add_le_add attempted control
  cases found : (PaidVertexAmplification.samples one (extra+1) bits).1 with
  | none =>
    simpa only [run,PaidVertexAmplification.samplesWithCharges_reference,found] using
      sampling.trans (Nat.le_add_right _ (work extra B C))
  | some result =>
    rcases result with ⟨cuts,rest⟩
    have scorePaid := select_charge score extra (fun i => (cuts i).1) (fun i => fits (cuts i).1)
    simpa only [run,PaidVertexAmplification.samplesWithCharges_reference,found] using Nat.add_le_add sampling scorePaid

end DirectedFlowCutGap.MeasuredTapeSelection
