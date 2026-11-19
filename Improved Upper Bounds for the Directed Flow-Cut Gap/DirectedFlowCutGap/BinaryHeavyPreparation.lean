import DirectedFlowCutGap.BinaryCubeThreshold
import DirectedFlowCutGap.BinaryVertexReductionArithmetic

/-! Binary threshold tests and retained doubled weights before size rounding. -/

namespace DirectedFlowCutGap.BinaryHeavyPreparation

open RawNonnegativeRational EncodedUnitCostReplication EncodedHeavyVertexPreparation
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)
open VertexReductionWidths (InputFits)

def build {n : ℕ} (D : Input n) (t : Code) : Residual n × ℕ :=
  let mask := batch fun i => BinaryRawRational.le t D.weights[i.val]
  let double := batch fun i => BinaryRawRational.mul (Code.ofNat 2) D.weights[i.val]
  (buildWith D mask.1 (fun i => double.1[i.val]),mask.2+double.2+6)

@[simp] theorem build_value {n : ℕ} (D : Input n) (t : Code) : (build D t).1=EncodedHeavyVertexPreparation.build D t := by
  simp only [build,batch_value,BinaryRawRational.le_value,BinaryRawRational.mul_value,Vector.getElem_ofFn,
    EncodedHeavyVertexPreparation.build,heavyMask]

private theorem build_paid {n b B : ℕ} (D : Input n) (t : Code)
    (fits : InputFits D b) (hb : b ≤ B) (ht : t.Bounded B) (h2 : 1 ≤ B) :
    (build D t).2 ≤ 2*(n*BinaryRawRational.budget B+8*n+4)+6 := by
  have binary (i : Fin n) := Code.bounded_mono (fits.weights i) hb
  have mask := batch_paid (fun i : Fin n => BinaryRawRational.le t D.weights[i.val])
    (fun i => BinaryRawRational.le_paid ht (binary i))
  have two : (Code.ofNat 2).Bounded 1 := ⟨by decide,by decide⟩
  have weight := batch_paid (fun i : Fin n => BinaryRawRational.mul (Code.ofNat 2) D.weights[i.val])
    (fun i => BinaryRawRational.mul_paid (Code.bounded_mono two h2) (binary i))
  unfold build
  dsimp only
  omega

def prepare {n : ℕ} (D : Input n) : (Residual n × ℕ) × ℕ :=
  let t := BinaryCubeThreshold.compute n
  let save := build D t.threshold
  ((save.1,t.wordWork+save.1.work+4),t.paid+save.2+4)

@[simp] theorem prepare_value {n : ℕ} (D : Input n) : (prepare D).1=EncodedHeavyVertexPreparation.prepare D := by
  have eq := BinaryCubeThreshold.compute_value n
  have a := congrArg Prod.fst eq
  have b := congrArg Prod.snd eq
  change (BinaryCubeThreshold.compute n).threshold=EncodedCubeRootThreshold.threshold n at a
  change (BinaryCubeThreshold.compute n).wordWork=(EncodedCubeRootThreshold.thresholdWithCost n).2 at b
  simp only [prepare,build_value,a,b,EncodedHeavyVertexPreparation.prepare,EncodedCubeRootThreshold.thresholdWithCost_value]

def budget {R : Type*} [Semiring R] (n b : R) : R :=
  BinaryCubeThreshold.budget n+2*(n*BinaryRawRational.budget (b+4*(n+1)+1)+8*n+4)+10

theorem prepare_paid {n b : ℕ} (D : Input n) (fits : InputFits D b) : (prepare D).2 ≤ budget n b := by
  let t := BinaryCubeThreshold.compute n
  let B := b+4*(n+1)+1
  have valid : t.threshold.Bounded B := by
    have e : t.threshold=EncodedCubeRootThreshold.threshold n := congrArg Prod.fst (BinaryCubeThreshold.compute_value n)
    rw [e]
    have size : (4*EncodedCubeRootThreshold.ceilCube n).size ≤ 4*(n+1) := (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      (Nat.mul_le_mul_left 4 (EncodedCubeRootThreshold.ceilCube_upper n))
    exact Code.bounded_mono (EncodedCubeRootThreshold.threshold_bounded n) (size.trans (by unfold B; omega))
  have work := build_paid D t.threshold fits (show b≤B by unfold B; omega) valid (by unfold B; omega)
  have time := BinaryCubeThreshold.compute_paid n
  change t.paid+(build D t.threshold).2+4 ≤ _
  change t.paid ≤ _ at time
  unfold budget
  change _ ≤ BinaryCubeThreshold.budget n+2*(n*BinaryRawRational.budget B+8*n+4)+10
  omega

end DirectedFlowCutGap.BinaryHeavyPreparation
