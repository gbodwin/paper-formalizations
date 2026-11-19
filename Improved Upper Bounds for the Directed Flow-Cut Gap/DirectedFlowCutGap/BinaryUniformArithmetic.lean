import DirectedFlowCutGap.BinaryVertexReductionArithmetic

/-! Binary clipping, average, ratios and ceiling counts for the uniform chain. -/

namespace DirectedFlowCutGap.BinaryUniformArithmetic

open RawNonnegativeRational EncodedUnitCostReplication EncodedUniformWeightParameters
open EncodedPortPreparation
open BinaryVertexReductionArithmetic (batch batch_value batch_paid ceilings ceilings_value ceilings_paid)
open VertexReductionWidths (InputFits uniformWidth)

def clip (q : Code) : Code × ℕ :=
  let test := BinaryRawRational.le Code.one q
  (if test.1 then Code.one else q,test.2+4)

@[simp] theorem clip_value (q : Code) : (clip q).1=clipOne q := by
  simp only [clip,BinaryRawRational.le_value,clipOne]

theorem clip_paid {q : Code} {B : ℕ} (fit : q.Bounded B) : (clip q).2 ≤ BinaryRawRational.budget B+4 :=
  Nat.add_le_add_right (BinaryRawRational.le_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _)) fit) _

private def port {n : ℕ} (D : Input n) : Port n → Code × ℕ
  | .inl i => clip D.weights[i.val]
  | .inr _ => (Code.zero,2)

private theorem port_value {n : ℕ} (D : Input n) (i : Port n) : (port D i).1=portWeight D i := by
  cases i <;> simp [port,portWeight]

def ports {n : ℕ} (D : Input n) : Input (3*n) × ℕ :=
  let weights := batch fun i => port D (decodePort i)
  let adjacency := Vector.ofFn (n:=3*n) fun i => Vector.ofFn (n:=3*n) fun j => portAdj D (decodePort i) (decodePort j)
  (⟨adjacency,weights.1,Vector.replicate (3*n) Code.one⟩,weights.2)

@[simp] theorem ports_value {n : ℕ} (D : Input n) : (ports D).1=portInput D := by
  simp only [ports,batch_value,port_value,portInput]

theorem ports_paid {n b : ℕ} (D : Input n) (fits : InputFits D b) :
    (ports D).2 ≤ (3*n)*(BinaryRawRational.budget b+4)+8*(3*n)+4 := by
  apply batch_paid
  intro i
  cases h : decodePort i with
  | inl v => simpa only [h,port] using clip_paid (fits.weights v)
  | inr v => simp only [port]; omega

def compute {n : ℕ} (D : Input n) : Parameters n × ℕ :=
  let m := 3*n
  let P := ports D
  let sums := BinaryVertexReductionArithmetic.totals P.1
  let average := BinaryRawRational.div sums.1.weight (Code.ofNat m)
  let ratios := batch fun i => BinaryRawRational.div P.1.weights[i.val] average.1
  let count := ceilings ratios.1
  ({ ports := P.1, total := sums.1.weight, average := average.1, ratios := ratios.1, counts := count.1
     work := 80*m^2+80*m+20+sums.1.work+80*m+30 }, P.2+sums.2+average.2+ratios.2+count.2+8)

@[simp] theorem compute_value {n : ℕ} (D : Input n) : (compute D).1=EncodedUniformWeightParameters.compute D := by
  simp only [compute,ports_value,BinaryVertexReductionArithmetic.totals_value,BinaryRawRational.div_value,
    batch_value,ceilings_value,EncodedUniformWeightParameters.compute]

def cutoff (q : Code) : ℕ × ℕ :=
  let inv := BinaryRawRational.div Code.one q
  let c := BinaryRawRational.ceil inv.1
  (c.1,inv.2+c.2+4)

@[simp] theorem cutoff_value (q : Code) : (cutoff q).1=(Code.one.div q).ceil := by
  simp only [cutoff,BinaryRawRational.ceil_value,BinaryRawRational.div_value]

theorem cutoff_paid {q : Code} {B : ℕ} (fits : q.Bounded B) :
    (cutoff q).2 ≤ 2*BinaryRawRational.budget B+4 := by
  have inv : ((BinaryRawRational.div Code.one q).1).Bounded B := by
    rw [BinaryRawRational.div_value]
    simpa only [Nat.zero_add] using Code.bounded_div Code.bounded_one fits
  have a := BinaryRawRational.div_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _)) fits
  have b := BinaryRawRational.ceil_paid inv
  unfold cutoff
  dsimp only
  omega

def budget {R : Type*} [Semiring R] (n b : R) : R :=
  let m := 3*n
  let W := uniformWidth n b
  m*(BinaryRawRational.budget b+4)+8*m+4+
    (m*(3*BinaryRawRational.budget (BinaryVertexReductionArithmetic.aggregateWidth m b)+10)+1)+
    BinaryRawRational.budget W+(m*BinaryRawRational.budget W+8*m+4)+
    (m*(BinaryRawRational.budget W+4)+8*m+4)+8

theorem compute_paid {n b : ℕ} (D : Input n) (fits : InputFits D b) : (compute D).2 ≤ budget n b := by
  let m := 3*n
  let W := uniformWidth n b
  let P := ports D
  let sums := BinaryVertexReductionArithmetic.totals P.1
  let average := BinaryRawRational.div sums.1.weight (Code.ofNat m)
  let ratios := batch (fun i : Fin m => BinaryRawRational.div P.1.weights[i.val] average.1)
  have hp := ports_paid D fits
  have H : InputFits P.1 b := by
    rw [show P.1=portInput D from ports_value D]
    refine ⟨port_weights_bounded D b fits.weights,?_⟩
    intro i
    simpa [portInput] using Code.bounded_mono Code.bounded_one (Nat.zero_le b)
  have ht := BinaryVertexReductionArithmetic.totals_paid P.1 H
  obtain ⟨wt,av,ra⟩ := VertexReductionWidths.uniform_fields D fits
  have eq := compute_value D
  have w : sums.1.weight.Bounded W := by
    have e : sums.1.weight=(EncodedUniformWeightParameters.compute D).total := congrArg Parameters.total eq
    rw [e]
    exact wt
  have f : (Code.ofNat m).Bounded W := by
    apply Code.bounded_mono (a:=m) (show (Code.ofNat m).Bounded m from ⟨Nat.lt_two_pow_self.le,Nat.one_le_two_pow⟩)
    unfold W uniformWidth m
    omega
  have hA := BinaryRawRational.div_paid w f
  have af : average.1.Bounded W := by
    have e : average.1=(EncodedUniformWeightParameters.compute D).average := congrArg Parameters.average eq
    rw [e]
    exact av
  have rr := batch_paid (fun i : Fin m => BinaryRawRational.div P.1.weights[i.val] average.1) (fun i =>
    BinaryRawRational.div_paid (Code.bounded_mono (H.weights i) (by unfold W uniformWidth; omega)) af)
  have cr : (ceilings ratios.1).2 ≤ m*(BinaryRawRational.budget W+4)+8*m+4 := by
    apply ceilings_paid
    intro i
    have e : ratios.1=(EncodedUniformWeightParameters.compute D).ratios := congrArg Parameters.ratios eq
    rw [e]
    exact ra i
  change P.2+sums.2+average.2+ratios.2+(ceilings ratios.1).2+8 ≤ _
  change P.2 ≤ m*(BinaryRawRational.budget b+4)+8*m+4 at hp
  change sums.2 ≤ m*(3*BinaryRawRational.budget (BinaryVertexReductionArithmetic.aggregateWidth m b)+10)+1 at ht
  change average.2 ≤ _ at hA
  change ratios.2 ≤ _ at rr
  unfold budget
  dsimp only
  change _ ≤ m*(BinaryRawRational.budget b+4)+8*m+4+
    (m*(3*BinaryRawRational.budget (BinaryVertexReductionArithmetic.aggregateWidth m b)+10)+1)+
    BinaryRawRational.budget W+(m*BinaryRawRational.budget W+8*m+4)+(m*(BinaryRawRational.budget W+4)+8*m+4)+8
  omega

end DirectedFlowCutGap.BinaryUniformArithmetic
