import DirectedFlowCutGap.MeasuredMultiplicityForms
import DirectedFlowCutGap.ConcurrentEdgeBudgetSelection

/-! Compute the exact rational sixth-power score with binary operations.
The score itself compares the existing two real sparsity scales. -/
namespace DirectedFlowCutGap.MeasuredSparsityScore

open scoped BigOperators NNRat
open RawNonnegativeRational (Code)
open MeasuredMultiplicityUpdate (ofNat_fits)
open FractionalCoverRawCore (rational)
open ChargedVertexModes (Mode)

private theorem work_mono {a b : ℕ} (ordered : a ≤ b) :
    BinaryRawRational.budget a ≤ BinaryRawRational.budget b := by
  unfold BinaryRawRational.budget
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right ordered 3) 2)

def power (q : Code) : ℕ → Code × ℕ
  | 0 => (Code.one,0)
  | k+1 =>
    let prior := power q k
    let next := BinaryRawRational.mul prior.1 q
    (next.1,prior.2+next.2)

@[simp] theorem power_value (q : Code) (k : ℕ) : (power q k).1.value = q.value^k := by
  induction k with
  | zero => simp [power]
  | succ k ih => simp only [power,BinaryRawRational.mul_value,Code.value_mul,ih,pow_succ]

theorem power_fits (q : Code) {B : ℕ} (fit : q.Bounded B) (k : ℕ) :
    (power q k).1.Bounded (k*B) := by
  induction k with
  | zero => simpa only [power,Nat.zero_mul] using Code.bounded_one
  | succ k ih =>
    simp only [power,BinaryRawRational.mul_value,Nat.add_mul,Nat.one_mul]
    exact Code.bounded_mul ih fit

theorem power_charge (q : Code) {B : ℕ} (fit : q.Bounded B) (k : ℕ) :
    (power q k).2 ≤ k*BinaryRawRational.budget (max B (k*B)) := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    let W := max B ((k+1)*B)
    have prev : k*B ≤ (k+1)*B := Nat.mul_le_mul_right B (Nat.le_succ k)
    have hi : max B (k*B) ≤ W :=
      max_le (le_max_left ..) (prev.trans (le_max_right ..))
    have old := ih.trans (Nat.mul_le_mul_left k (work_mono hi))
    have fee := BinaryRawRational.mul_paid (Code.bounded_mono (power_fits q fit k) (prev.trans (le_max_right B _)))
      (Code.bounded_mono fit (le_max_left B ((k+1)*B)))
    change (power q k).2+(BinaryRawRational.mul (power q k).1 q).2 ≤ (k+1)*BinaryRawRational.budget W
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add old fee

def reciprocal (j : ℕ) : Code × ℕ := BinaryRawRational.div Code.one (Code.ofNat (j+1))

private def harmonicCells (m : ℕ) : List (Code × ℕ) := List.ofFn (fun i : Fin m => reciprocal i.val)

def harmonic (m : ℕ) : Code × ℕ :=
  let terms := harmonicCells m
  let total := MeasuredMultiplicityForms.sum (terms.map Prod.fst)
  (total.1,(terms.map Prod.snd).sum+total.2)

theorem harmonic_value (m : ℕ) : (harmonic m).1.value = NormalizedOptimalMode.harmonic m := by
  apply Subtype.ext
  change rational (harmonic m).1 = (NormalizedOptimalMode.harmonic m : ℚ)
  simp only [harmonic,harmonicCells,MeasuredMultiplicityForms.sum_value,FractionalCoverRawCore.rational_sum,
    List.map_ofFn,Function.comp_def,reciprocal,BinaryRawRational.div_value,FractionalCoverRawCore.rational_div,
    FractionalCoverRawCore.rational_one,FractionalCoverRawCore.rational_nat,List.sum_ofFn,
    NormalizedOptimalMode.harmonic,NNRat.cast_sum,NNRat.coe_div,NNRat.coe_one,NNRat.coe_natCast]

theorem harmonic_bounds (m : ℕ) :
    (harmonic m).1.Bounded (m*(m+1)) ∧
      (harmonic m).2 ≤ m*BinaryRawRational.budget m+m*BinaryRawRational.budget (m*(m+1)) := by
  have fit (i : Fin m) : (Code.ofNat (i.val+1)).Bounded m :=
    ofNat_fits ((Nat.succ_le_of_lt i.isLt).trans Nat.lt_two_pow_self.le)
  have ingredient (i : Fin m) : (reciprocal i.val).1.Bounded m := by
    simp only [reciprocal,BinaryRawRational.div_value]
    simpa only [Nat.zero_add] using Code.bounded_div Code.bounded_one (fit i)
  let items := (harmonicCells m).map Prod.fst
  have size : items.length = m := by simp [items,harmonicCells]
  have each (q : Code) (found : q ∈ items) : q.Bounded m := by
    simp only [items,harmonicCells,List.map_ofFn,Function.comp_def,List.mem_ofFn] at found
    obtain ⟨i,rfl⟩ := found
    exact ingredient i
  have totalFit := FractionalCoverRawCore.sumCodes_bounded items m each
  have totalWork := MeasuredMultiplicityForms.sum_charge items each size.le
  rw [size] at totalFit totalWork
  have eachFee (i : Fin m) : (reciprocal i.val).2 ≤ BinaryRawRational.budget m :=
    BinaryRawRational.div_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _)) (fit i)
  have spent : ((harmonicCells m).map Prod.snd).sum ≤ m*BinaryRawRational.budget m := by
    simp only [harmonicCells,List.map_ofFn,Function.comp_def,List.sum_ofFn]
    exact (Finset.sum_le_sum (fun i _ => eachFee i)).trans_eq (by simp)
  exact ⟨by simpa only [harmonic,MeasuredMultiplicityForms.sum_value,items] using totalFit,
    Nat.add_le_add spent totalWork⟩

private def factor (n : ℕ) (mass h : Code) (mode : Mode) : Code × ℕ :=
  match mode with
  | .size =>
    let size := power (Code.ofNat n) 2
    let weight := power h 6
    let value := BinaryRawRational.mul size.1 weight.1
    (value.1,size.2+weight.2+value.2)
  | .mass =>
    let weight := power h 9
    let volume := power mass 3
    let value := BinaryRawRational.mul weight.1 volume.1
    (value.1,weight.2+volume.2+value.2)

def score (n m : ℕ) (amount mass h : Code) (mode : Mode) : Code × ℕ :=
  let mean := BinaryRawRational.div amount (Code.ofNat m)
  let common := power mean.1 6
  let chosen := factor n mass h mode
  let result := BinaryRawRational.mul common.1 chosen.1
  (result.1,mean.2+common.2+chosen.2+result.2)

theorem score_value (n m : ℕ) (amount mass h : Code) (mode : Mode)
    (correct : h.value = NormalizedOptimalMode.harmonic m) :
    (score n m amount mass h mode).1.value = ConcurrentEdgeBudgetSelection.score n m amount.value mass.value mode := by
  cases mode <;> simp only [score,factor,ConcurrentEdgeBudgetSelection.score,BinaryRawRational.div_value,
    BinaryRawRational.mul_value,Code.value_div,Code.value_mul,Code.value_ofNat,power_value,correct]

private theorem power_under (q : Code) {B W : ℕ} (fit : q.Bounded B) (k : ℕ) (base : B ≤ W) (pow : k*B ≤ W) :
    (power q k).2 ≤ k*BinaryRawRational.budget W :=
  (power_charge q fit k).trans (Nat.mul_le_mul_left k (work_mono (max_le base pow)))

def factorWidth (n M H : ℕ) : ℕ := 2*n+9*H+3*M

attribute [local irreducible] BinaryRawRational.mul in
private theorem factor_bounds (n : ℕ) (mass h : Code) (mode : Mode) {M H W : ℕ}
    (massFit : mass.Bounded M) (weightFit : h.Bounded H) (size : factorWidth n M H ≤ W) :
    (factor n mass h mode).1.Bounded (factorWidth n M H) ∧
      (factor n mass h mode).2 ≤ 13*BinaryRawRational.budget W := by
  unfold factorWidth at size ⊢
  cases mode with
  | size =>
    have dim : (Code.ofNat n).Bounded n := ofNat_fits Nat.lt_two_pow_self.le
    have aa := power_fits (Code.ofNat n) dim 2
    have bb := power_fits h weightFit 6
    have paidDim := power_under (Code.ofNat n) dim 2 (by omega : n ≤ W) (by omega : 2*n ≤ W)
    have paidWeight := power_under h weightFit 6 (by omega : H ≤ W) (by omega : 6*H ≤ W)
    have paidMul := BinaryRawRational.mul_paid (Code.bounded_mono aa (by omega : 2*n ≤ W))
      (Code.bounded_mono bb (by omega : 6*H ≤ W))
    constructor
    · simp only [factor,BinaryRawRational.mul_value]
      exact Code.bounded_mono (Code.bounded_mul aa bb) (by omega)
    · dsimp only [factor]
      omega
  | mass =>
    have aa := power_fits h weightFit 9
    have bb := power_fits mass massFit 3
    have paidH := power_under h weightFit 9 (by omega : H ≤ W) (by omega : 9*H ≤ W)
    have paidMass := power_under mass massFit 3 (by omega : M ≤ W) (by omega : 3*M ≤ W)
    have paidMul := BinaryRawRational.mul_paid (Code.bounded_mono aa (by omega : 9*H ≤ W))
      (Code.bounded_mono bb (by omega : 3*M ≤ W))
    constructor
    · simp only [factor,BinaryRawRational.mul_value]
      exact Code.bounded_mono (Code.bounded_mul aa bb) (by omega)
    · dsimp only [factor]
      omega

def scoreWidth (n m B M H : ℕ) : ℕ := 6*(B+m)+factorWidth n M H

attribute [local irreducible] BinaryRawRational.div BinaryRawRational.mul in
theorem score_bounds (n m : ℕ) (amount mass h : Code) (mode : Mode) {B M H : ℕ}
    (amountFit : amount.Bounded B) (massFit : mass.Bounded M) (weightFit : h.Bounded H) :
    let W := scoreWidth n m B M H
    (score n m amount mass h mode).1.Bounded W ∧ (score n m amount mass h mode).2 ≤ 21*BinaryRawRational.budget W := by
  let W := scoreWidth n m B M H
  let avg := BinaryRawRational.div amount (Code.ofNat m)
  have dimensions : (Code.ofNat m).Bounded m := ofNat_fits Nat.lt_two_pow_self.le
  have entry : avg.1.Bounded (B+m) := by
    change (BinaryRawRational.div amount (Code.ofNat m)).1.Bounded _
    rw [BinaryRawRational.div_value]
    exact Code.bounded_div amountFit dimensions
  have big : 6*(B+m) ≤ W := Nat.le_add_right ..
  have more : factorWidth n M H ≤ W := Nat.le_add_left ..
  have base : B+m ≤ W := (by omega : B+m ≤ 6*(B+m)).trans big
  have readAvg : avg.2 ≤ BinaryRawRational.budget W :=
    BinaryRawRational.div_paid (Code.bounded_mono amountFit ((Nat.le_add_right ..).trans base))
      (Code.bounded_mono dimensions ((Nat.le_add_left ..).trans base))
  have commonBounds := power_fits avg.1 entry 6
  have commonPaid := power_under avg.1 entry 6 base big
  obtain ⟨factorFit,factorPaid⟩ := factor_bounds n mass h mode massFit weightFit more
  have last := BinaryRawRational.mul_paid (Code.bounded_mono commonBounds big) (Code.bounded_mono factorFit more)
  constructor
  · simp only [score,BinaryRawRational.mul_value]
    exact Code.bounded_mul commonBounds factorFit
  · change avg.2+(power avg.1 6).2+(factor n mass h mode).2+
      (BinaryRawRational.mul (power avg.1 6).1 (factor n mass h mode).1).2 ≤ 21*BinaryRawRational.budget W
    omega

end DirectedFlowCutGap.MeasuredSparsityScore
