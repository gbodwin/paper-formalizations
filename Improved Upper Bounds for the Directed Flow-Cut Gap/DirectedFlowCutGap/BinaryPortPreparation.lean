import DirectedFlowCutGap.BinaryUniformArithmetic

/-! Binary low-mask and retained core-weight operations for the weighted
vertex preparation, followed by the measured binary replication arithmetic. -/

namespace DirectedFlowCutGap.BinaryPortPreparation

open RawNonnegativeRational EncodedUnitCostReplication EncodedPortPreparation
open EncodedUnitCostPreparation
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)
open VertexReductionWidths (InputFits)

private def dataWith {n : ℕ} (D : Input n) (low : Vector Bool n) : EncodedShortcutReachability.Input (3*n) :=
  { adjacency := Vector.ofFn (fun i => Vector.ofFn (fun j => portAdj D (decodePort i) (decodePort j)))
    removed := Vector.ofFn fun i => match decodePort i with
      | .inl v => low[v.val]
      | .inr _ => false }

private def weightWith {n : ℕ} (weights : Vector Code n) : Port n → Code
  | .inl v => weights[v.val]
  | .inr _ => Code.zero

private def doubled (q : Code) : Code × ℕ :=
  let mul := BinaryRawRational.mul (Code.ofNat 2) q
  let clip := BinaryUniformArithmetic.clip mul.1
  (clip.1,mul.2+clip.2+4)

def build {n : ℕ} (D : Input n) : Prepared n × ℕ :=
  let threshold := BinaryRawRational.div Code.one (Code.ofNat (2*n))
  let low := batch (fun i => BinaryRawRational.le D.weights[i.val] threshold.1)
  let weights := batch (fun i => doubled D.weights[i.val])
  (buildWith D (dataWith D low.1) (weightWith weights.1),threshold.2+low.2+weights.2+8)

@[simp] theorem build_value {n : ℕ} (D : Input n) : (build D).1=EncodedUnitCostPreparation.build D := by
  let low := batch (fun i : Fin n => BinaryRawRational.le D.weights[i.val]
    (BinaryRawRational.div Code.one (Code.ofNat (2*n))).1)
  let weights := batch (fun i : Fin n => doubled D.weights[i.val])
  have eq : low.1=lowMask D := by simp only [low,batch_value,BinaryRawRational.div_value,BinaryRawRational.le_value,lowMask]
  have data : dataWith D low.1=portData D := by rw [eq]; rfl
  have w : weightWith weights.1=preparedWeightCode D := by
    funext x
    cases x with
    | inl v => simp only [weights,batch_value,weightWith,Vector.getElem_ofFn,doubled,BinaryRawRational.mul_value,
        BinaryUniformArithmetic.clip_value,preparedWeightCode]
    | inr p => rfl
  change buildWith D (dataWith D low.1) (weightWith weights.1)=_
  rw [data,w]
  rfl

def portBudget {R : Type*} [Semiring R] (n b : R) : R :=
  let W := b+2*n+1
  BinaryRawRational.budget W+(n*BinaryRawRational.budget W+8*n+4)+
    (n*(2*BinaryRawRational.budget W+8)+8*n+4)+8

private theorem build_paid {n b : ℕ} (D : Input n) (fits : InputFits D b) : (build D).2 ≤ portBudget n b := by
  let W := b+2*n+1
  let q := BinaryRawRational.div Code.one (Code.ofNat (2*n))
  have base : (Code.ofNat (2*n)).Bounded (2*n) := ⟨(2*n).lt_two_pow_self.le,Nat.one_le_two_pow⟩
  have hn : (Code.ofNat (2*n)).Bounded W :=
    Code.bounded_mono base (by unfold W; omega)
  have h := BinaryRawRational.div_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _)) hn
  have fit : q.1.Bounded W := by
    change (BinaryRawRational.div Code.one _).1.Bounded _
    rw [BinaryRawRational.div_value]
    simpa only [Nat.zero_add] using Code.bounded_div Code.bounded_one hn
  have low := batch_paid (fun i : Fin n => BinaryRawRational.le D.weights[i.val] q.1)
    (fun i => BinaryRawRational.le_paid (Code.bounded_mono (fits.weights i) (by unfold W; omega)) fit)
  have weights := batch_paid (fun i : Fin n => doubled D.weights[i.val]) (cap:=2*BinaryRawRational.budget W+8) (fun i => by
    have two : (Code.ofNat 2).Bounded 1 := ⟨by decide,by decide⟩
    have twoW : (Code.ofNat 2).Bounded W := Code.bounded_mono two (by unfold W; omega)
    have weightW := Code.bounded_mono (fits.weights i) (show b ≤ W by unfold W; omega)
    have mul := BinaryRawRational.mul_paid twoW weightW
    have bounded : (BinaryRawRational.mul (Code.ofNat 2) D.weights[i.val]).1.Bounded W := by
      rw [BinaryRawRational.mul_value]
      exact Code.bounded_mono (Code.bounded_mul two (fits.weights i)) (by unfold W; omega)
    have clip := BinaryUniformArithmetic.clip_paid bounded
    unfold doubled
    dsimp only
    change (BinaryRawRational.mul (Code.ofNat 2) D.weights[i.val]).2 ≤ BinaryRawRational.budget W at mul
    omega)
  change q.2+(batch (fun i : Fin n => BinaryRawRational.le D.weights[i.val] q.1)).2+
    (batch (fun i : Fin n => doubled D.weights[i.val])).2+8 ≤ _
  unfold portBudget
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h low) weights) _

def prepareAndReduce {n : ℕ} (D : Input n) : EncodedUnitCostPreparation.Reduction n × ℕ :=
  let p := build D
  let r := BinaryVertexReductionArithmetic.reduce p.1.data
  (⟨p.1,r.1⟩,p.2+r.2+4)

@[simp] theorem prepareAndReduce_value {n : ℕ} (D : Input n) :
    (prepareAndReduce D).1=EncodedUnitCostPreparation.prepareAndReduce D := by
  simp only [prepareAndReduce,BinaryVertexReductionArithmetic.reduce_value]
  exact congrArg (fun p : Prepared n => (⟨p,p.data.reduce⟩ : Reduction n)) (build_value D)

theorem prepareAndReduce_paid {n b : ℕ} (D : Input n) (fits : InputFits D b) :
    (prepareAndReduce D).2 ≤ portBudget n b+BinaryVertexReductionArithmetic.reductionBudget (3*n) (b+1)+4 := by
  have w : InputFits (build D).1.data (b+1) := (build_value D).symm ▸ VertexReductionWidths.prepared_fields D fits
  have h := BinaryVertexReductionArithmetic.reduce_paid (build D).1.data w
  have size : (build D).1.size ≤ 3*n := (build_value D).symm ▸ build_size_le D
  have larger : BinaryVertexReductionArithmetic.reductionBudget (build D).1.size (b+1) ≤
      BinaryVertexReductionArithmetic.reductionBudget (3*n) (b+1) := by
    unfold BinaryVertexReductionArithmetic.reductionBudget BinaryVertexReductionArithmetic.aggregateWidth
      BinaryVertexReductionArithmetic.normalizedWidth BinaryRawRational.budget
    gcongr
  exact Nat.add_le_add_right (Nat.add_le_add (build_paid D fits) (h.trans larger)) _

end DirectedFlowCutGap.BinaryPortPreparation
