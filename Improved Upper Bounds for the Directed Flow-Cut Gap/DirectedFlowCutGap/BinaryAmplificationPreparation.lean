import DirectedFlowCutGap.BinaryNaturalOperations
import DirectedFlowCutGap.BinaryFractionalGuessesBounds
import DirectedFlowCutGap.ChargedPhysicalVertexSolver
import DirectedFlowCutGap.BinaryVertexReductionArithmetic

/-! The amplified sampler prepares one decoded copy of the original prices
and computes the exact trial cap using charged binary operations. -/
namespace DirectedFlowCutGap.BinaryAmplificationPreparation

open BinaryArithmetic BinaryFractionalRows BinaryRational
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)
open BinaryNaturalOperations (size_le_self)

structure Prepared (n : ℕ) where
  costs : FractionalCoverRawCore.RawRow n
  trials : ℕ
  paid : ℕ

private theorem width_eq (n : ℕ) : max 1 n.size=FairBitWords.width n := by
  by_cases h : 0<n
  · rw [BinaryBoundedSampler.size_eq_width h,max_eq_right]
    exact FairBitWords.width_pos n
  · have zero : n=0 := by omega
    subst n
    decide

def prepare {n : ℕ} (costs : Row n) (draw extra confidence : ℕ) : Prepared n :=
  let prices := batch fun i => BinaryRawRational.decode (get costs i)
  let widest := BinaryFractionalGuesses.inputWidth costs
  let dimension := BinaryNaturalView.encode n
  let grid := BinaryFractionalGuesses.gridFuel dimension.1 widest.1
  let length := BinaryNaturalView.decode grid.1
  let repeats := BinaryNaturalOperations.add extra 1
  let draws := BinaryNaturalOperations.mul length.1 draw
  let calls := BinaryNaturalOperations.mul repeats.1 draws.1
  let width := BinaryNaturalOperations.width calls.1
  let trials := BinaryNaturalOperations.add (max 1 width.1) confidence
  ⟨prices.1,trials.1,prices.2+widest.2+dimension.2+grid.2+length.2+repeats.2+draws.2+calls.2+
    width.2+trials.2+16*(width.1+1)+12⟩

@[simp] theorem costs_value {n : ℕ} (costs : Row n) (draw extra confidence : ℕ) :
    (prepare costs draw extra confidence).costs=decodeRow costs := by
  simp only [prepare,batch_value,BinaryRawRational.decode_value,decodeRow]

@[simp] theorem trials_value {n : ℕ} (D : BinaryFractionalGuesses.Input n) (draw extra confidence : ℕ) :
    (prepare D.costs draw extra confidence).trials=ChargedPhysicalVertexSolver.trialLimit
      (BinaryFractionalGuesses.decodeInput D) draw extra confidence := by
  simp only [prepare,BinaryNaturalOperations.add_value,BinaryNaturalOperations.mul_value,
    BinaryNaturalOperations.width_value,BinaryNaturalView.decode_value,width_eq,
    BinaryFractionalGuesses.gridFuel_value,BinaryNaturalView.encode_value,BinaryFractionalGuesses.inputWidth_value,
    ChargedPhysicalVertexSolver.trialLimit,FairBitConfidence.trials,EncodedVertexSolver.drawBound]
  rfl

private def controlWidth {R : Type*} [Semiring R] (x : R) : R :=
  (x+1)*(4*x+4)*(x+1)+4*x+8

def budget {R : Type*} [Semiring R] (x : R) : R :=
  let W := controlWidth x
  x*(40*(x+1)^2)+8*x+4+
    (x*(128*(x+2)^2+17*(x+2)+10)+1+2*x+4)+16*(x+1)^2+
    4096*(4*x+6)^2+16*(4*x+5)^2+
    4*(BinaryRawRational.budget W+4)+(24*(W+1)^2+4)+16*(W+1)+12

theorem budget_mono {a b : ℕ} (h : a ≤ b) : budget a ≤ budget b := by
  unfold budget controlWidth BinaryRawRational.budget
  dsimp only
  gcongr

open Polynomial in
theorem budget_eval (p : Polynomial ℕ) (x : ℕ) :
    (budget p).eval x=budget (p.eval x) := by
  simp only [budget,controlWidth,BinaryRawRational.budget,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat]

set_option maxHeartbeats 1200000 in
theorem prepare_paid {n B x : ℕ} (costs : Row n) (draw extra confidence : ℕ)
    (fit : ∀ i, StoredBounded (get costs i) B)
    (hn : n ≤ x) (hB : B ≤ x) (hd : draw ≤ x) (he : extra ≤ x) (hc : confidence ≤ x) :
    (prepare costs draw extra confidence).paid ≤ budget x := by
  let widened := BinaryFractionalGuesses.inputWidth costs
  let dimension := BinaryNaturalView.encode n
  let grid := BinaryFractionalGuesses.gridFuel dimension.1 widened.1
  let length := BinaryNaturalView.decode grid.1
  let repeats := BinaryNaturalOperations.add extra 1
  let draws := BinaryNaturalOperations.mul length.1 draw
  let calls := BinaryNaturalOperations.mul repeats.1 draws.1
  let width := BinaryNaturalOperations.width calls.1
  let cap := BinaryNaturalOperations.add (max 1 width.1) confidence
  let W := controlWidth x
  have prices := batch_paid (fun i => BinaryRawRational.decode (get costs i))
    (fun i => BinaryRawRational.decode_paid (fit i))
  have prices' : n*(40*(B+1)^2)+8*n+4 ≤ x*(40*(x+1)^2)+8*x+4 := by gcongr
  have widest := BinaryFractionalGuessesBounds.inputWidth_bounds costs fit
  have widest' : BinaryFractionalGuessesBounds.inputWidthBound n B ≤ x*(128*(x+2)^2+17*(x+2)+10)+1+2*x+4 := by
    unfold BinaryFractionalGuessesBounds.inputWidthBound BinaryFractionalGuessesBounds.widthListBound
    gcongr
  have hdim : value dimension.1=n := BinaryNaturalView.encode_value n
  have dlen : dimension.1.length≤n+1 := by
    rw [show dimension.1=n.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
    exact (size_le_self _).trans (Nat.le_succ _)
  have dpaid := (BinaryNaturalView.encode_paid n).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right ((size_le_self _).trans hn) 1) 2))
  obtain ⟨gl,gw,gp⟩ := BinaryFractionalGuessesBounds.gridFuel_bounds dimension.1 widened.1 hdim dlen widest.1 widest.2.1
  have gridBound : BinaryFractionalGuessesBounds.gridBound n B ≤ 4*x+4 := by
    unfold BinaryFractionalGuessesBounds.gridBound
    omega
  have gridPaid : BinaryFractionalGuessesBounds.gridCharge n B ≤ 4096*(4*x+6)^2 := by
    unfold BinaryFractionalGuessesBounds.gridCharge
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right gridBound 2) 2)
  have gwidth := gw.trans gridBound
  have lengthPaid := (BinaryNaturalView.decode_paid grid.1).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right gwidth 1) 2))
  have lengthValue : length.1 ≤ 4*x+4 :=
    (BinaryNaturalView.decode_value _).trans_le (gl.trans gridBound)
  have xw : x+1≤W := by unfold W controlWidth; omega
  have lw : 4*x+4≤W := by unfold W controlWidth; omega
  have repl : repeats.1 ≤ x+1 := (BinaryNaturalOperations.add_value _ _).trans_le (Nat.add_le_add_right he 1)
  have qlim : draws.1 ≤ (4*x+4)*(x+1) := by
    change (BinaryNaturalOperations.mul length.1 draw).1 ≤ _
    rw [BinaryNaturalOperations.mul_value]
    exact Nat.mul_le_mul lengthValue (hd.trans (Nat.le_succ _))
  have drawW : draws.1 ≤ W := by
    apply qlim.trans
    unfold W controlWidth
    have h := Nat.mul_le_mul_right ((4*x+4)*(x+1)) (show 1 ≤ x+1 by omega)
    simp only [Nat.one_mul, Nat.mul_assoc] at h ⊢
    omega
  have callsW : calls.1 ≤ W := by
    change (BinaryNaturalOperations.mul repeats.1 draws.1).1 ≤ _
    rw [BinaryNaturalOperations.mul_value]
    apply le_trans (Nat.mul_le_mul repl qlim)
    unfold W controlWidth
    simp only [Nat.mul_assoc]
    omega
  have rw' : repeats.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.add_paid ((size_le_self _).trans (he.trans (by omega))) ((size_le_self 1).trans (by omega))
  have dw' : draws.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.mul_paid ((size_le_self _).trans (lengthValue.trans lw)) ((size_le_self _).trans (hd.trans (by omega)))
  have cw' : calls.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.mul_paid ((size_le_self _).trans (repl.trans xw)) ((size_le_self _).trans drawW)
  have ww' : width.2 ≤ 24*(W+1)^2+4 := BinaryNaturalOperations.width_paid ((size_le_self _).trans callsW)
  have widthW : width.1 ≤ W := (BinaryNaturalOperations.width_value _).trans_le ((size_le_self _).trans callsW)
  have tw' : cap.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.add_paid ((size_le_self _).trans (max_le (by omega) widthW))
      ((size_le_self _).trans (hc.trans (by omega)))
  change (batch fun i => BinaryRawRational.decode (get costs i)).2+widened.2+dimension.2+grid.2+length.2+
    repeats.2+draws.2+calls.2+width.2+cap.2+16*(width.1+1)+12 ≤ budget x
  change dimension.2 ≤ 16*(x+1)^2 at dpaid
  change length.2 ≤ 16*(4*x+5)^2 at lengthPaid
  have wp := widest.2.2.trans widest'
  have gp' := gp.trans gridPaid
  have pr := prices.trans prices'
  change widened.2 ≤ _ at wp
  change grid.2 ≤ _ at gp'
  unfold budget
  change _ ≤ x*(40*(x+1)^2)+8*x+4+ (x*(128*(x+2)^2+17*(x+2)+10)+1+2*x+4)+
    16*(x+1)^2+4096*(4*x+6)^2+16*(4*x+5)^2+
    4*(BinaryRawRational.budget W+4)+(24*(W+1)^2+4)+16*(W+1)+12
  omega

attribute [irreducible] prepare

end DirectedFlowCutGap.BinaryAmplificationPreparation
