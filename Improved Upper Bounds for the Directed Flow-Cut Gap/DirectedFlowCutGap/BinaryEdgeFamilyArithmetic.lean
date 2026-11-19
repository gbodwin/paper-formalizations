import DirectedFlowCutGap.BinaryRationalNormalize
import DirectedFlowCutGap.BinaryVertexReductionArithmetic
import DirectedFlowCutGap.ChargedEdgeThresholdDemands
import DirectedFlowCutGap.AdaptiveWidthEnvelope

/-! Binary arithmetic for the original weights, multiplicative update
factors, and adaptive penalties. The row index is the original edge pair. -/

namespace DirectedFlowCutGap.BinaryEdgeFamilyArithmetic

open scoped NNRat BigOperators
open BinaryArithmetic BinaryRational RawNonnegativeRational
open RandomizedEdgeFamily RationalEdgeDecomposition
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)

abbrev Row (n : ℕ) := Vector Code (n*n)

def read {n : ℕ} (row : Row n) (e : Edge n) : Code := row[(finProdFinEquiv e).val]

def Fits {n : ℕ} (row : Row n) (B : ℕ) : Prop := ∀ i : Fin (n*n), row[i.val].Bounded B

theorem Fits.mono {n a b : ℕ} {row : Row n} (h : Fits row a) (le : a ≤ b) : Fits row b :=
  fun i => Code.bounded_mono (h i) le

private theorem sum_finRange {m : ℕ} {A : Type*} [AddCommMonoid A] (f : Fin m → A) :
    ((List.finRange m).map f).sum = ∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange m)]
  congr 1
  ext i
  simp

private def scanInput {n : ℕ} (w p : Row n) : EncodedUnitCostReplication.Input (n*n) :=
  ⟨Vector.replicate (n*n) (Vector.replicate (n*n) false),w,p⟩

def sums {n : ℕ} (w p : Row n) : EncodedUnitCostReplication.Input.Totals × ℕ :=
  let result := BinaryVertexReductionArithmetic.totals (scanInput w p)
  (result.1,result.2+8*(n*n)+8)

theorem sums_weight {n : ℕ} (w p : Row n) : (sums w p).1.weight.value = ∑ e : Edge n, (read w e).value := by
  simp only [sums,BinaryVertexReductionArithmetic.totals_value,EncodedUnitCostReplication.Input.totals,
    EncodedUnitCostReplication.Input.scan_weight,sum_finRange,scanInput]
  exact ((finProdFinEquiv : Edge n ≃ Fin (n*n)).sum_comp fun i => w[i.val].value).symm

theorem sums_objective {n : ℕ} (w p : Row n) :
    (sums w p).1.objective.value = ∑ e : Edge n, (read p e).value*(read w e).value := by
  simp only [sums,BinaryVertexReductionArithmetic.totals_value,EncodedUnitCostReplication.Input.totals,
    EncodedUnitCostReplication.Input.scan_objective,sum_finRange,scanInput]
  exact ((finProdFinEquiv : Edge n ≃ Fin (n*n)).sum_comp fun i => p[i.val].value*w[i.val].value).symm

theorem sums_bounds {n B : ℕ} (w p : Row n) (hw : Fits w B) (hp : Fits p B) :
    (sums w p).1.weight.Bounded (n*n*(B+1)) ∧
      (sums w p).1.objective.Bounded (n*n*(2*B+1)) := by
  have h := (scanInput w p).scan_bounded B hw hp (List.finRange (n*n))
  simpa only [sums,BinaryVertexReductionArithmetic.totals_value,EncodedUnitCostReplication.Input.totals,
    List.length_finRange] using h

def sumBudget {R : Type*} [Semiring R] (n B : R) : R :=
  n*n*(3*BinaryRawRational.budget (BinaryVertexReductionArithmetic.aggregateWidth (n*n) B)+10)+1+8*(n*n)+8

theorem sums_paid {n B : ℕ} (w p : Row n) (hw : Fits w B) (hp : Fits p B) :
    (sums w p).2 ≤ sumBudget n B :=
  Nat.add_le_add_right (Nat.add_le_add_right
    (BinaryVertexReductionArithmetic.totals_paid (scanInput w p) ⟨hw,hp⟩) _) _

private def originalAt {n : ℕ} (D : Input n) (e : Edge n) : Code × ℕ :=
  if D.adjacency[e.1.val][e.2.val] then BinaryRawRational.decode D.weights[e.1.val][e.2.val]
  else (Code.zero,4)

def originals {n : ℕ} (D : Input n) : Row n × ℕ :=
  batch fun i => originalAt D (finProdFinEquiv.symm i)

theorem originals_value {n : ℕ} (D : Input n) (e : Edge n) :
    (read (originals D).1 e).value=originalWeight D.adjacency D.weights e := by
  simp only [originals,read,batch_value,Vector.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]
  rcases e with ⟨u,v⟩
  cases h : D.adjacency[u.val][v.val] <;>
    simp [originalAt,originalWeight,h,weightQ,RationalEdgeThresholds.cost,BinaryFractionalWalkOracle.decodeCost]

theorem originals_width {n B : ℕ} (D : Input n)
    (fit : AdaptiveWidthEnvelope.StoredWeights D.weights B) : Fits (originals D).1 B := by
  intro i
  simp only [originals,batch_value,Vector.getElem_ofFn,Fin.eta]
  let e : Edge n := finProdFinEquiv.symm i
  change (originalAt D e).1.Bounded B
  by_cases h : D.adjacency[e.1.val][e.2.val]=true
  · simp only [originalAt,ite_eq_left h,BinaryRawRational.decode_value]
    exact BinaryFractionalRows.stored_raw_bound (fit e.1 e.2)
  · simp only [originalAt,ite_eq_right h]
    exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)

theorem originals_paid {n B : ℕ} (D : Input n) (fit : AdaptiveWidthEnvelope.StoredWeights D.weights B) :
    (originals D).2 ≤ n*n*(40*(B+1)^2)+8*(n*n)+4 := by
  apply batch_paid
  intro i
  let e : Edge n := finProdFinEquiv.symm i
  change (originalAt D e).2 ≤ _
  by_cases h : D.adjacency[e.1.val][e.2.val]=true
  · simp only [originalAt,ite_eq_left h]
    exact BinaryRawRational.decode_paid (fit e.1 e.2)
  · simp only [originalAt,ite_eq_right h]
    have unit : 1 ≤ (B+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega

private def adjust (cutoff q : Code) : Code × ℕ :=
  let cmp := BinaryRawRational.le q cutoff
  if cmp.1 then (Code.zero,cmp.2+4) else
    let doubled := BinaryRawRational.mul (Code.ofNat 2) q
    (doubled.1,cmp.2+doubled.2+6)

private theorem adjust_value (cutoff q : Code) :
    (adjust cutoff q).1.value=if q.value≤cutoff.value then 0 else 2*q.value := by
  by_cases h : q.value≤cutoff.value
  · have cmp := (Code.le_eq_true q cutoff).mpr h
    simp only [adjust,BinaryRawRational.le_value,ite_eq_left h,ite_eq_left cmp,Code.value_zero]
  · have cmp := fun eq => h ((Code.le_eq_true q cutoff).mp eq)
    simp only [adjust,BinaryRawRational.le_value,ite_eq_right h,ite_eq_right cmp,BinaryRawRational.mul_value,
      Code.value_mul,Code.value_ofNat,Nat.cast_ofNat]

private def maxField (a b : Code) : Code × ℕ :=
  let cmp := BinaryRawRational.le a b
  (if cmp.1 then b else a,cmp.2+4)

private theorem maxField_value (a b : Code) : (maxField a b).1.value=max a.value b.value := by
  by_cases h : a.value≤b.value
  · have cmp := (Code.le_eq_true a b).mpr h
    simp only [maxField,BinaryRawRational.le_value,ite_eq_left cmp,max_eq_right h]
  · have cmp := fun eq => h ((Code.le_eq_true a b).mp eq)
    simp only [maxField,BinaryRawRational.le_value,ite_eq_right cmp,max_eq_left (le_of_not_ge h)]

private def gain (floor scale factor : Code) : Code × ℕ :=
  let product := BinaryRawRational.mul floor factor
  let ratio := BinaryRawRational.div scale product.1
  let update := BinaryRawRational.add Code.one ratio.1
  (update.1,product.2+ratio.2+update.2+8)

private theorem gain_value (floor scale factor : Code) :
    (gain floor scale factor).1.value = 1+scale.value/(floor.value*factor.value) := by
  simp only [gain,BinaryRawRational.mul_value,BinaryRawRational.div_value,BinaryRawRational.add_value,
    Code.value_mul,Code.value_div,Code.value_add,Code.value_one]

private def floorGain (floor weight cutoff factor : Code) : Code × ℕ :=
  let q := maxField floor weight
  let step := gain q.1 cutoff factor
  (step.1,q.2+step.2+4)

structure Preparation (n : ℕ) where
  adjusted : Row n
  gain : Row n
  total : Code
  factor : Code

def prepare {n : ℕ} (D : Input n) : Preparation n × ℕ :=
  let source := originals D
  let cutoff := BinaryRawRational.div Code.one (Code.ofNat (2*n))
  let floor := BinaryRawRational.div Code.one (Code.ofNat n)
  let factor := Code.ofNNRat D.factor
  let adjusted := batch fun i => adjust cutoff.1 source.1[i.val]
  let change := batch fun i => floorGain floor.1 adjusted.1[i.val] cutoff.1 factor
  let total := sums source.1 (Vector.replicate (n*n) Code.one)
  (⟨adjusted.1,change.1,total.1.weight,factor⟩,source.2+cutoff.2+floor.2+adjusted.2+change.2+total.2+16)

theorem prepare_adjusted {n : ℕ} (D : Input n) (e : Edge n) :
    (read (prepare D).1.adjusted e).value=RandomizedEdgeFamily.adjusted D e := by
  simp only [prepare,read,batch_value,Vector.getElem_ofFn,adjust_value,
    BinaryRawRational.div_value,Code.value_div,Code.value_one,Code.value_ofNat,Nat.cast_mul,Nat.cast_ofNat,
    RandomizedEdgeFamily.adjusted,modifiedWeight,one_div]
  rw [show (originals D).1[(finProdFinEquiv e).val].value=originalWeight D.adjacency D.weights e from originals_value D e]

theorem prepare_gain {n : ℕ} (D : Input n) (e : Edge n) :
    (read (prepare D).1.gain e).value=1+scale n/(floored D e*D.factor) := by
  let p := prepare D
  let floor := BinaryRawRational.div Code.one (Code.ofNat n)
  let cutoff := BinaryRawRational.div Code.one (Code.ofNat (2*n))
  have h : (read p.1.gain e).value =
      (gain (maxField floor.1 (read p.1.adjusted e)).1 cutoff.1 (Code.ofNNRat D.factor)).1.value := by
    unfold p prepare read
    simp only [batch_value,Vector.getElem_ofFn,floorGain]
    rfl
  rw [h,gain_value,maxField_value,prepare_adjusted]
  simp only [floor,cutoff,BinaryRawRational.div_value,Code.value_div,Code.value_one,Code.value_ofNat,
    Code.value_ofNNRat,Nat.cast_mul,Nat.cast_ofNat,one_div,floored,scale]

theorem prepare_total {n : ℕ} (D : Input n) :
    (prepare D).1.total.value=originalTotal D.adjacency D.weights := by
  simp only [prepare,sums_weight,originals_value,originalTotal]

@[simp] theorem prepare_factor {n : ℕ} (D : Input n) : (prepare D).1.factor.value=D.factor :=
  Code.value_ofNNRat _

private theorem natural_fit (n : ℕ) : (Code.ofNat n).Bounded n :=
  ⟨n.lt_two_pow_self.le,Nat.one_le_two_pow⟩

private theorem reciprocal_width (k : ℕ) :
    (BinaryRawRational.div Code.one (Code.ofNat k)).1.Bounded k := by
  rw [BinaryRawRational.div_value]
  simpa only [Nat.zero_add] using Code.bounded_div Code.bounded_one (natural_fit k)

private theorem reciprocal_paid {k B : ℕ} (h : k ≤ B) :
    (BinaryRawRational.div Code.one (Code.ofNat k)).2 ≤ BinaryRawRational.budget B :=
  BinaryRawRational.div_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _)) (Code.bounded_mono (natural_fit k) h)

private theorem two_width : (Code.ofNat 2).Bounded 1 := ⟨by decide,by decide⟩

private theorem adjust_width {cut q : Code} {B : ℕ} (hq : q.Bounded B) :
    (adjust cut q).1.Bounded (B+1) := by
  unfold adjust
  dsimp only
  split
  · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)
  · rw [BinaryRawRational.mul_value]
    simpa only [Nat.add_comm] using Code.bounded_mul two_width hq

private theorem adjust_paid {cut q : Code} {B : ℕ} (hc : cut.Bounded B) (hq : q.Bounded B) (h : 1 ≤ B) :
    (adjust cut q).2 ≤ 2*BinaryRawRational.budget B+6 := by
  have cmp := BinaryRawRational.le_paid hq hc
  have dbl := BinaryRawRational.mul_paid (Code.bounded_mono two_width h) hq
  unfold adjust
  dsimp only
  split <;> omega

private theorem maxField_fits {a b : Code} {B : ℕ} (ha : a.Bounded B) (hb : b.Bounded B) :
    (maxField a b).1.Bounded B ∧ (maxField a b).2 ≤ BinaryRawRational.budget B+4 := by
  constructor
  · unfold maxField
    dsimp only
    split
    · exact hb
    · exact ha
  · exact Nat.add_le_add_right (BinaryRawRational.le_paid ha hb) _

private theorem gain_fits {q η α : Code} {B : ℕ} (hq : q.Bounded B) (he : η.Bounded B) (ha : α.Bounded B) :
    (gain q η α).1.Bounded (3*B+1) ∧ (gain q η α).2 ≤ 3*BinaryRawRational.budget (3*B+1)+8 := by
  let W := 3*B+1
  let product := BinaryRawRational.mul q α
  let ratio := BinaryRawRational.div η product.1
  have product_fit : product.1.Bounded (B+B) := by
    change (BinaryRawRational.mul q α).1.Bounded _
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul hq ha
  have ratio_fit : ratio.1.Bounded (3*B) := by
    change (BinaryRawRational.div η product.1).1.Bounded _
    rw [BinaryRawRational.div_value]
    exact Code.bounded_mono (Code.bounded_div he product_fit) (by omega)
  constructor
  · change (BinaryRawRational.add Code.one ratio.1).1.Bounded _
    rw [BinaryRawRational.add_value]
    simpa only [Nat.zero_add] using Code.bounded_add Code.bounded_one ratio_fit
  · have small : B ≤ W := by unfold W; omega
    have p := BinaryRawRational.mul_paid (Code.bounded_mono hq small) (Code.bounded_mono ha small)
    have r := BinaryRawRational.div_paid (Code.bounded_mono he small)
      (Code.bounded_mono product_fit (show B+B ≤ W by unfold W; omega))
    have a := BinaryRawRational.add_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le W))
      (Code.bounded_mono ratio_fit (Nat.le_succ _))
    change product.2 ≤ _ at p
    change ratio.2 ≤ _ at r
    change product.2+ratio.2+(BinaryRawRational.add Code.one ratio.1).2+8 ≤ 3*BinaryRawRational.budget W+8
    omega

private theorem floorGain_fits {f w η α : Code} {B : ℕ}
    (hf : f.Bounded B) (hw : w.Bounded B) (hη : η.Bounded B) (hα : α.Bounded B) :
    (floorGain f w η α).1.Bounded (3*B+1) ∧
      (floorGain f w η α).2 ≤ BinaryRawRational.budget B+3*BinaryRawRational.budget (3*B+1)+16 := by
  obtain ⟨sq,sqPaid⟩ := maxField_fits hf hw
  obtain ⟨a,aPaid⟩ := gain_fits sq hη hα
  exact ⟨a,(Nat.add_le_add_right (Nat.add_le_add sqPaid aPaid) 4).trans (by omega)⟩

def setupWidth {R : Type*} [Semiring R] (n B : R) : R := B+2*n+1

def prepareBudget {R : Type*} [Semiring R] (n B : R) : R :=
  let W := setupWidth n B
  let m := n*n
  (m*(40*(B+1)^2)+8*m+4)+2*BinaryRawRational.budget W+
    (m*(2*BinaryRawRational.budget W+6)+8*m+4)+
    (m*(BinaryRawRational.budget W+3*BinaryRawRational.budget (3*W+1)+16)+8*m+4)+sumBudget n B+16

set_option maxHeartbeats 1400000 in
theorem prepare_fits_paid {n B : ℕ} (D : Input n) (sourceFits : AdaptiveWidthEnvelope.StoredWeights D.weights B)
    (factorFits : NNRatStoredBounds.Bounded D.factor B) :
    Fits (prepare D).1.adjusted (B+1) ∧
    Fits (prepare D).1.gain (3*setupWidth n B+1) ∧
    (prepare D).1.total.Bounded (n*n*(B+1)) ∧ (prepare D).2 ≤ prepareBudget n B := by
  let p := prepare D
  let source := originals D
  let cut := BinaryRawRational.div Code.one (Code.ofNat (2*n))
  let floor := BinaryRawRational.div Code.one (Code.ofNat n)
  let α := Code.ofNNRat D.factor
  let w := batch fun i => adjust cut.1 source.1[i.val]
  let update := fun i : Fin (n*n) => floorGain floor.1 w.1[i.val] cut.1 α
  let W := setupWidth n B
  have orig : Fits source.1 B := originals_width D sourceFits
  have sourceFit : Fits source.1 W := orig.mono (by unfold W setupWidth; omega)
  have cutFit : cut.1.Bounded W := Code.bounded_mono (reciprocal_width _) (by unfold W setupWidth; omega)
  have floorFit : floor.1.Bounded W := Code.bounded_mono (reciprocal_width _) (by unfold W setupWidth; omega)
  have factorFit : α.Bounded W := Code.bounded_mono factorFits (by unfold W setupWidth; omega)
  have wg : Fits w.1 (B+1) := by
    intro i
    simp only [w,batch_value,Vector.getElem_ofFn]
    exact adjust_width (orig i)
  have wo : Fits w.1 W := wg.mono (by unfold W setupWidth; omega)
  have g (i : Fin (n*n)) : (update i).1.Bounded (3*W+1) ∧
      (update i).2 ≤ BinaryRawRational.budget W+3*BinaryRawRational.budget (3*W+1)+16 :=
    floorGain_fits floorFit (wo i) cutFit factorFit
  have gg : Fits (batch update).1 (3*W+1) := by
    intro i
    simp only [batch_value,Vector.getElem_ofFn]
    exact (g i).1
  have oneRow : Fits (Vector.replicate (n*n) Code.one) B := fun i => by
    simpa only [Vector.getElem_replicate] using Code.bounded_mono Code.bounded_one (Nat.zero_le B)
  have totalFit := (sums_bounds source.1 _ orig oneRow).1
  refine ⟨wg,gg,totalFit,?_⟩
  have a := originals_paid D sourceFits
  have c := reciprocal_paid (show 2*n ≤ W by unfold W setupWidth; omega)
  have f := reciprocal_paid (show n ≤ W by unfold W setupWidth; omega)
  have ws := batch_paid (fun i => adjust cut.1 source.1[i.val])
    (fun i => adjust_paid cutFit (sourceFit i) (show 1 ≤ W by unfold W setupWidth; omega))
  have gs := batch_paid update (fun i => (g i).2)
  have ss := sums_paid source.1 _ orig oneRow
  change source.2 ≤ _ at a
  change cut.2 ≤ _ at c
  change floor.2 ≤ _ at f
  change w.2 ≤ _ at ws
  change source.2+cut.2+floor.2+w.2+(batch update).2+(sums source.1 (Vector.replicate (n*n) Code.one)).2+16 ≤
    (n*n*(40*(B+1)^2)+8*(n*n)+4)+2*BinaryRawRational.budget W+
      (n*n*(2*BinaryRawRational.budget W+6)+8*(n*n)+4)+
      (n*n*(BinaryRawRational.budget W+3*BinaryRawRational.budget (3*W+1)+16)+8*(n*n)+4)+sumBudget n B+16
  omega

end DirectedFlowCutGap.BinaryEdgeFamilyArithmetic
