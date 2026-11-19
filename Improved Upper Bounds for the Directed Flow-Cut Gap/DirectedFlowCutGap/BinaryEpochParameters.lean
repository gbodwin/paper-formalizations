import DirectedFlowCutGap.BinaryNaturalOperations
import DirectedFlowCutGap.EncodedEpochParameters

/-! The cutoff gate's restart, exponent and cap are computed using the
binary logarithm and the measured natural operations. -/

namespace DirectedFlowCutGap.BinaryEpochParameters

open BinaryArithmetic BinaryDivision
open BinaryNaturalOperations (size_le_self)

structure LogResult where
  exponent : ℕ
  wordWork : ℕ
  paid : ℕ

def floorLog (base : Bits) : ℕ → Bits → LogResult
  | 0,_ => ⟨0,1,8⟩
  | k+1,x =>
    let cmp := lessEqual base x
    let valid := lessEqual [false,true] base
    let overhead := cmp.2+valid.2+16*(k+2)+24
    if cmp.1 && valid.1 then
      let q := divide x base
      let tail := floorLog base k q.quotient
      ⟨tail.exponent+1,tail.wordWork+12,tail.paid+q.steps+overhead⟩
    else ⟨0,6,overhead⟩

private theorem gate (b x : Bits) :
    ((lessEqual b x).1 && (lessEqual [false,true] b).1)=true ↔ value b ≤ value x ∧ 1 < value b := by
  simp only [Bool.and_eq_true,(lessEqual_spec ..).1]
  change _ ∧ 2 ≤ value b ↔ _
  omega

theorem floorLog_pair (b x : Bits) (k : ℕ) :
    ((floorLog b k x).exponent,(floorLog b k x).wordWork)=EncodedEpochParameters.floorLog (value b) k (value x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    by_cases good : value b ≤ value x ∧ 1 < value b
    · simp only [floorLog,EncodedEpochParameters.floorLog,ite_eq_left good,ite_eq_left ((gate b x).mpr good)]
      have h := ih (divide x b).quotient
      rw [(divide_spec x b).1] at h
      rw [← h]
    · have no : ¬((lessEqual b x).1 && (lessEqual [false,true] b).1)=true := fun t => good ((gate b x).mp t)
      simp only [floorLog,EncodedEpochParameters.floorLog,ite_eq_right good,ite_eq_right no]

theorem floorLog_exponent (b x : Bits) (k : ℕ) :
    (floorLog b k x).exponent=(EncodedEpochParameters.floorLog (value b) k (value x)).1 :=
  congrArg Prod.fst (floorLog_pair b x k)

theorem floorLog_words (b x : Bits) (k : ℕ) :
    (floorLog b k x).wordWork=(EncodedEpochParameters.floorLog (value b) k (value x)).2 :=
  congrArg Prod.snd (floorLog_pair b x k)

def logStepBudget {R : Type*} [Semiring R] (B k : R) : R :=
  1024*(B+1)^2+34*(B+1)+16*(k+1)+24

def logBudget {R : Type*} [Semiring R] (B k : R) : R := k*logStepBudget B k+8

theorem floorLog_paid {B : ℕ} (b x : Bits) (k : ℕ) (bFit : b.length ≤ B) (xFit : x.length ≤ B) (large : 2 ≤ B) :
    (floorLog b k x).paid ≤ logBudget B k := by
  induction k generalizing x with
  | zero => simp [floorLog,logBudget]
  | succ k ih =>
    have cmp := (lessEqual_spec b x).2.trans (Nat.mul_le_mul_left 17
      (Nat.add_le_add_right (max_le bFit xFit) 1))
    have base := (lessEqual_spec [false,true] b).2.trans (Nat.mul_le_mul_left 17
      (Nat.add_le_add_right (max_le (show ([false,true] : Bits).length ≤ B from large) bFit) 1))
    let q := divide x b
    have h := divide_charge_bound xFit bFit
    have width : q.quotient.length ≤ B := by
      rw [(divide_spec x b).2.2.1]
      exact (Nat.size_le_size (Nat.div_le_self _ _)).trans ((Nat.size_le.mpr (value_lt x)).trans xFit)
    have old := ih q.quotient width
    have mono : logStepBudget B k ≤ logStepBudget B (k+1) := by unfold logStepBudget; omega
    have tail := old.trans (Nat.add_le_add_right (Nat.mul_le_mul_left k mono) 8)
    change (floorLog b k (divide x b).quotient).paid ≤ _ at tail
    unfold floorLog logBudget
    dsimp only
    rw [Nat.add_mul,Nat.one_mul]
    unfold logStepBudget at *
    split <;> (try dsimp only) <;> omega

structure Result where
  parameters : EncodedEpochParameters.Parameters
  paid : ℕ

def compute (n : ℕ) : Result :=
  let start := BinaryNaturalOperations.add n 2
  let w := BinaryNaturalView.encode start.1
  let a := floorLog [false,true] start.1 w.1
  let ratio := BinaryNaturalOperations.add a.exponent 2
  let base := BinaryNaturalView.encode ratio.1
  let sq := BinaryNaturalOperations.mul n n
  let cube := BinaryNaturalOperations.mul sq.1 n
  let x := BinaryNaturalView.encode cube.1
  let b := floorLog base.1 cube.1 x.1
  let fuel := BinaryNaturalOperations.add b.exponent 1
  let exponent := BinaryNaturalOperations.mul 2 fuel.1
  let cap := BinaryNaturalOperations.powerTwo exponent.1
  ⟨⟨ratio.1,fuel.1,cap.1,a.wordWork+b.wordWork+6*fuel.1+1+16⟩,
    start.2+w.2+a.paid+ratio.2+base.2+sq.2+cube.2+x.2+b.paid+fuel.2+exponent.2+cap.2+32⟩

set_option maxHeartbeats 800000 in
theorem compute_value (n : ℕ) : (compute n).parameters=EncodedEpochParameters.compute n := by
  have two : value [false,true] = 2 := rfl
  simp only [compute,floorLog_exponent,floorLog_words,two,BinaryNaturalView.encode_value,
    BinaryNaturalOperations.add_value,BinaryNaturalOperations.mul_value,BinaryNaturalOperations.powerTwo_value,
    EncodedEpochParameters.compute,EncodedEpochParameters.powerFour_value,EncodedEpochParameters.powerFour_work,
    pow_mul,show (2:ℕ)^2 = 4 by decide,Nat.add_assoc]

def setupWidth {R : Type*} [Semiring R] (n : R) : R := 4*(n+3)^3+12

def budget {R : Type*} [Semiring R] (n : R) : R :=
  let W := setupWidth n
  6*(BinaryRawRational.budget W+4)+48*(W+1)^2+2*logBudget W W+24*(W+2)^2+36

set_option maxHeartbeats 1400000 in
theorem compute_paid (n : ℕ) : (compute n).paid ≤ budget n := by
  let start := BinaryNaturalOperations.add n 2
  let w := BinaryNaturalView.encode start.1
  let a := floorLog [false,true] start.1 w.1
  let ratio := BinaryNaturalOperations.add a.exponent 2
  let base := BinaryNaturalView.encode ratio.1
  let sq := BinaryNaturalOperations.mul n n
  let cube := BinaryNaturalOperations.mul sq.1 n
  let x := BinaryNaturalView.encode cube.1
  let b := floorLog base.1 cube.1 x.1
  let fuel := BinaryNaturalOperations.add b.exponent 1
  let exponent := BinaryNaturalOperations.mul 2 fuel.1
  let cap := BinaryNaturalOperations.powerTwo exponent.1
  let W := setupWidth n
  have nW : n ≤ W := by unfold W setupWidth; nlinarith [sq_nonneg n, Nat.zero_le (n^3)]
  have twoW : 2 ≤ W := by unfold W setupWidth; omega
  have startLen : start.1 ≤ W := by
    change (BinaryNaturalOperations.add n 2).1 ≤ _
    rw [BinaryNaturalOperations.add_value]
    unfold W setupWidth
    nlinarith [sq_nonneg n, Nat.zero_le (n^3)]
  have sz : sq.1 ≤ W := by
    change (BinaryNaturalOperations.mul n n).1 ≤ _
    rw [BinaryNaturalOperations.mul_value]
    unfold W setupWidth
    nlinarith [sq_nonneg n, Nat.zero_le (n^3)]
  have cubeEq : cube.1=n*n*n := by simp only [cube,sq,BinaryNaturalOperations.mul_value]
  have cubeLen : cube.1 ≤ W := by
    rw [cubeEq]; unfold W setupWidth
    nlinarith [sq_nonneg n, Nat.zero_le (n^3)]
  have aLen : a.exponent ≤ n+2 := by
    change (floorLog [false,true] start.1 w.1).exponent ≤ _
    rw [floorLog_exponent,show value [false,true]=2 from rfl,show value w.1=start.1 from BinaryNaturalView.encode_value _,
      EncodedEpochParameters.floorLog_value _ _ _ le_rfl,
      show start.1=n+2 from BinaryNaturalOperations.add_value _ _]
    exact Nat.log_le_self ..
  have bLen : b.exponent ≤ cube.1 := by
    change (floorLog base.1 cube.1 x.1).exponent ≤ _
    rw [floorLog_exponent,show value x.1=cube.1 from BinaryNaturalView.encode_value _,
      EncodedEpochParameters.floorLog_value _ _ _ le_rfl]
    exact Nat.log_le_self ..
  have ratioLen : ratio.1 ≤ W := by
    rw [show ratio.1=a.exponent+2 from BinaryNaturalOperations.add_value _ _]
    unfold W setupWidth
    nlinarith [sq_nonneg n, Nat.zero_le (n^3)]
  have powLen : exponent.1 ≤ W := by
    rw [show exponent.1=2*fuel.1 from BinaryNaturalOperations.mul_value _ _,
      show fuel.1=b.exponent+1 from BinaryNaturalOperations.add_value _ _]
    unfold W setupWidth
    rw [cubeEq] at bLen
    nlinarith [sq_nonneg n, Nat.zero_le (n^3)]
  have fuelLen : fuel.1 ≤ W := by
    have e : exponent.1=2*fuel.1 := BinaryNaturalOperations.mul_value _ _
    omega
  have oneW : (1:ℕ).size ≤ W := by exact (size_le_self 1).trans (by omega)
  have wordLen (z : ℕ) (h : z ≤ W) : (BinaryNaturalView.encode z).1.length ≤ W := by
    rw [BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]
    exact (size_le_self z).trans h
  have encoded (z : ℕ) (h : z ≤ W) : (BinaryNaturalView.encode z).2 ≤ 16*(W+1)^2 :=
    (BinaryNaturalView.encode_paid z).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right ((size_le_self z).trans h) 1) 2))
  have ws : w.2 ≤ 16*(W+1)^2 := encoded _ startLen
  have wb : base.2 ≤ 16*(W+1)^2 := encoded _ ratioLen
  have wx : x.2 ≤ 16*(W+1)^2 := encoded _ cubeLen
  have lmono {u : ℕ} (hu : u ≤ W) : logBudget W u ≤ logBudget W W := by
    unfold logBudget logStepBudget
    gcongr
  have la : a.paid ≤ logBudget W W :=
    (floorLog_paid _ _ _ twoW (wordLen _ startLen) twoW).trans (lmono startLen)
  have lb : b.paid ≤ logBudget W W :=
    (floorLog_paid _ _ _ (wordLen _ ratioLen) (wordLen _ cubeLen) twoW).trans (lmono cubeLen)
  have h1 : start.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.add_paid ((size_le_self _).trans nW) ((size_le_self _).trans twoW)
  have h2 : ratio.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.add_paid ((size_le_self _).trans (aLen.trans
      ((BinaryNaturalOperations.add_value n 2).symm.trans_le startLen))) ((size_le_self _).trans twoW)
  have h3 : sq.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.mul_paid ((size_le_self _).trans nW) ((size_le_self _).trans nW)
  have h4 : cube.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.mul_paid ((size_le_self _).trans sz) ((size_le_self _).trans nW)
  have h5 : fuel.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.add_paid ((size_le_self _).trans (bLen.trans cubeLen)) oneW
  have h6 : exponent.2 ≤ BinaryRawRational.budget W+4 :=
    BinaryNaturalOperations.mul_paid ((size_le_self _).trans twoW) ((size_le_self _).trans fuelLen)
  have h7 : cap.2 ≤ 24*(W+2)^2+4 := BinaryNaturalOperations.powerTwo_paid powLen
  change start.2+w.2+a.paid+ratio.2+base.2+sq.2+cube.2+x.2+b.paid+fuel.2+exponent.2+cap.2+32 ≤
    6*(BinaryRawRational.budget W+4)+48*(W+1)^2+2*logBudget W W+24*(W+2)^2+36
  omega

end DirectedFlowCutGap.BinaryEpochParameters
