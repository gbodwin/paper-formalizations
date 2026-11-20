import DirectedFlowCutGap.BinaryRawRational
import DirectedFlowCutGap.VertexReductionWidths
import DirectedFlowCutGap.BinaryArrayBatch

/-! Binary arithmetic for the aggregates, zero-objective flags, normalized
costs and ceilings used by vertex replication. The raw fields and counted
word-model outputs agree exactly with the existing reduction. -/

namespace DirectedFlowCutGap.BinaryVertexReductionArithmetic

open RawNonnegativeRational EncodedUnitCostReplication
open VertexReductionWidths (InputFits)

def batch {m : ℕ} {A : Type} (f : Fin m → A × ℕ) : Vector A m × ℕ :=
  (BinaryArrayBatch.run f).1

theorem batch_reference {m : ℕ} {A : Type} (f : Fin m → A × ℕ) :
    batch f = (let data := Vector.ofFn f
      (data.map Prod.fst,(data.toList.map Prod.snd).sum+8*m+4)) := by
  rw [batch,BinaryArrayBatch.run_value]
  apply Prod.ext
  · apply Vector.ext
    intro i fits
    simp
  · simp [Vector.toList_ofFn]

@[simp] theorem batch_value {m : ℕ} {A : Type} (f : Fin m → A × ℕ) :
    (batch f).1=Vector.ofFn (fun i => (f i).1) :=
  congrArg Prod.fst (BinaryArrayBatch.run_value f)

theorem batch_paid {m cap : ℕ} {A : Type} (f : Fin m → A × ℕ) (cost : ∀ i, (f i).2 ≤ cap) :
    (batch f).2 ≤ m*cap+8*m+4 := by
  have hs : (List.ofFn fun i => (f i).2).sum ≤ m*cap := by
    rw [List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin m, cap := Finset.sum_le_sum (fun i _ => cost i)
      _ = _ := by simp
  simp only [batch,BinaryArrayBatch.run_value,List.map_ofFn,Function.comp_def]
  exact Nat.add_le_add_right (Nat.add_le_add_right hs _) _

def scan {m : ℕ} (D : Input m) : List (Fin m) → Input.Totals × ℕ
  | [] => (⟨Code.zero,Code.zero,1⟩,1)
  | i::is =>
    let tail := scan D is
    let prod := BinaryRawRational.mul D.costs[i.val] D.weights[i.val]
    let sum := BinaryRawRational.add D.weights[i.val] tail.1.weight
    let objective := BinaryRawRational.add prod.1 tail.1.objective
    (⟨sum.1,objective.1,tail.1.work+29⟩,tail.2+prod.2+sum.2+objective.2+10)

@[simp] theorem scan_value {m : ℕ} (D : Input m) (is : List (Fin m)) : (scan D is).1=D.scan is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scan,Input.scan,ih,BinaryRawRational.mul_value,BinaryRawRational.add_value,
      Code.mulWithCost,Code.addWithCost]

def aggregateWidth {R : Type*} [Semiring R] (m b : R) : R := m*(2*b+1)+2*b+1

theorem scan_paid {m b cap : ℕ} (D : Input m) (fits : InputFits D b) (is : List (Fin m))
    (length : is.length ≤ cap) :
    (scan D is).2 ≤ is.length*(3*BinaryRawRational.budget (aggregateWidth cap b)+10)+1 := by
  let W := aggregateWidth cap b
  induction is with
  | nil => simp [scan]
  | cons i rest ih =>
    have hcard : rest.length ≤ cap := by simp only [List.length_cons] at length; omega
    have tail := ih hcard
    have hs := D.scan_bounded b fits.weights fits.costs rest
    have hobj : rest.length*(2*b+1) ≤ W := (Nat.mul_le_mul_right _ hcard).trans (by unfold W aggregateWidth; omega)
    have hw : rest.length*(b+1) ≤ W := (Nat.mul_le_mul_left _ (by omega)).trans hobj
    have scale : b ≤ W := by unfold W aggregateWidth; omega
    have width := Code.bounded_mono (fits.weights i) scale
    have price := Code.bounded_mono (fits.costs i) scale
    have prod : ((BinaryRawRational.mul D.costs[i.val] D.weights[i.val]).1).Bounded W := by
      rw [BinaryRawRational.mul_value]
      apply Code.bounded_mono (Code.bounded_mul (fits.costs i) (fits.weights i))
      unfold W aggregateWidth
      omega
    have pm := BinaryRawRational.mul_paid price width
    have ps := BinaryRawRational.add_paid width (Code.bounded_mono hs.1 hw)
    have po := BinaryRawRational.add_paid prod (Code.bounded_mono hs.2 hobj)
    simp only [scan,scan_value,List.length_cons,Nat.add_mul,Nat.one_mul]
    change (scan D rest).2 ≤ rest.length*(3*BinaryRawRational.budget W+10)+1 at tail
    change _ ≤ rest.length*(3*BinaryRawRational.budget W+10)+(3*BinaryRawRational.budget W+10)+1
    omega

def totals {m : ℕ} (D : Input m) : Input.Totals × ℕ := scan D (List.finRange m)

@[simp] theorem totals_value {m : ℕ} (D : Input m) : (totals D).1=D.totals := scan_value D _

theorem totals_paid {m b : ℕ} (D : Input m) (fits : InputFits D b) :
    (totals D).2 ≤ m*(3*BinaryRawRational.budget (aggregateWidth m b)+10)+1 := by
  simpa only [totals,List.length_finRange] using scan_paid D fits (List.finRange m) (cap:=m) (by simp)

private theorem ofNat_fit (n : ℕ) : (Code.ofNat n).Bounded n :=
  ⟨Nat.lt_two_pow_self.le,Nat.one_le_two_pow⟩

def normalized {m : ℕ} (D : Input m) (t : Input.Totals) : Vector Code m × ℕ :=
  let denom := BinaryRawRational.mul (Code.ofNat 2) t.objective
  let scale := BinaryRawRational.div t.weight denom.1
  let fields := batch fun i => BinaryRawRational.mul scale.1 D.costs[i.val]
  (fields.1,denom.2+scale.2+fields.2+6)

@[simp] theorem normalized_value {m : ℕ} (D : Input m) (t : Input.Totals) : (normalized D t).1=D.normalized t := by
  simp only [normalized,Input.normalized,batch_value,BinaryRawRational.mul_value,BinaryRawRational.div_value]

def normalizedWidth {R : Type*} [Semiring R] (m b : R) : R := m*(b+1)+(1+m*(2*b+1))+b+2

private theorem two_fit : (Code.ofNat 2).Bounded 1 := ⟨by decide,by decide⟩

theorem normalized_paid {m b : ℕ} (D : Input m) (fits : InputFits D b) :
    (normalized D D.totals).2 ≤ (m+2)*BinaryRawRational.budget (normalizedWidth m b)+8*m+10 := by
  let W := normalizedWidth m b
  let two := BinaryRawRational.mul (Code.ofNat 2) D.totals.objective
  let scale := BinaryRawRational.div D.totals.weight two.1
  have widths : D.totals.weight.Bounded (m*(b+1)) ∧ D.totals.objective.Bounded (m*(2*b+1)) := by
    simpa only [Input.totals,List.length_finRange] using D.scan_bounded b fits.weights fits.costs (List.finRange m)
  have u : 1 ≤ W := by unfold W normalizedWidth; omega
  have v : m*(2*b+1) ≤ W := by unfold W normalizedWidth; omega
  have s : m*(b+1) ≤ W := by unfold W normalizedWidth; omega
  have t : b ≤ W := by unfold W normalizedWidth; omega
  have hp := BinaryRawRational.mul_paid (Code.bounded_mono two_fit u) (Code.bounded_mono widths.2 v)
  have db : two.1.Bounded (1+m*(2*b+1)) := by
    dsimp only [two]
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul two_fit widths.2
  have hd := BinaryRawRational.div_paid (Code.bounded_mono widths.1 s)
    (Code.bounded_mono db (by unfold W normalizedWidth; omega))
  have bs : scale.1.Bounded W := by
    dsimp only [scale]
    rw [BinaryRawRational.div_value]
    exact Code.bounded_mono (Code.bounded_div widths.1 db) (by unfold W normalizedWidth; omega)
  have mm := batch_paid (fun i : Fin m => BinaryRawRational.mul scale.1 D.costs[i.val])
    (fun i => BinaryRawRational.mul_paid bs (Code.bounded_mono (fits.costs i) t))
  change two.2 ≤ BinaryRawRational.budget W at hp
  change scale.2 ≤ BinaryRawRational.budget W at hd
  change two.2+scale.2+(batch (fun i : Fin m => BinaryRawRational.mul scale.1 D.costs[i.val])).2+6 ≤ _
  rw [Nat.add_mul]
  change _ ≤ m*BinaryRawRational.budget W+2*BinaryRawRational.budget W+8*m+10
  omega

def ceilings {m : ℕ} (xs : Vector Code m) : Vector ℕ m × ℕ :=
  batch fun i =>
    let result := BinaryRawRational.ceil xs[i.val]
    (max 1 result.1,result.2+4)

@[simp] theorem ceilings_value {m : ℕ} (xs : Vector Code m) : (ceilings xs).1=Input.copyCounts xs := by
  simp only [ceilings,batch_value,BinaryRawRational.ceil_value,Input.copyCounts]

theorem ceilings_paid {m W : ℕ} (xs : Vector Code m) (fits : ∀ i : Fin m, xs[i.val].Bounded W) :
    (ceilings xs).2 ≤ m*(BinaryRawRational.budget W+4)+8*m+4 := by
  apply batch_paid
  intro i
  exact Nat.add_le_add_right (BinaryRawRational.ceil_paid (fits i)) _

def zeroMask {m : ℕ} (D : Input m) : Vector Bool m × ℕ :=
  batch fun i =>
    let scaled := BinaryRawRational.mul (Code.ofNat m) D.weights[i.val]
    let test := BinaryRawRational.le Code.one scaled.1
    (test.1,scaled.2+test.2+6)

@[simp] theorem zeroMask_value {m : ℕ} (D : Input m) : (zeroMask D).1=D.zeroMask := by
  simp only [zeroMask,batch_value,BinaryRawRational.le_value,BinaryRawRational.mul_value,Input.zeroMask]

theorem zeroMask_paid {m b : ℕ} (D : Input m) (fits : InputFits D b) :
    (zeroMask D).2 ≤ m*(2*BinaryRawRational.budget (m+b)+6)+8*m+4 := by
  apply batch_paid
  intro i
  have h := Code.bounded_mono (fits.weights i) (Nat.le_add_left b m)
  have p := BinaryRawRational.mul_paid (Code.bounded_mono (ofNat_fit m) (Nat.le_add_right m b)) h
  have w : (BinaryRawRational.mul (Code.ofNat m) D.weights[i.val]).1.Bounded (m+b) := by
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul (ofNat_fit m) (fits.weights i)
  have q := BinaryRawRational.le_paid (Code.bounded_mono Code.bounded_one (Nat.zero_le _)) w
  dsimp only
  omega

def reduce {m : ℕ} (D : Input m) : Input.Result m × ℕ :=
  let agg := totals D
  let word := BinaryNaturalView.encode agg.1.objective.num
  let test := BinaryArithmetic.isZero word.1
  let setup := agg.2+word.2+test.2+8
  if test.1 then
    let masks := zeroMask D
    (.zero masks.1 (agg.1.work+40*m+20),setup+masks.2)
  else
    let qs := normalized D agg.1
    let count := ceilings qs.1
    let out := materialize D count.1
    (.replicated qs.1 count.1 out (agg.1.work+out.work+60*m+40),setup+qs.2+count.2)

@[simp] theorem reduce_value {m : ℕ} (D : Input m) : (reduce D).1=D.reduce := by
  have zero : (BinaryArithmetic.isZero (BinaryNaturalView.encode (totals D).1.objective.num).1).1=true ↔
      D.totals.objective.num=0 := by
    rw [(BinaryArithmetic.isZero_spec _).1,BinaryNaturalView.encode_value,totals_value]
  by_cases h : D.totals.objective.num=0
  · unfold reduce
    dsimp only
    rw [ite_eq_left (zero.mpr h)]
    simp only [zeroMask_value,totals_value,Input.reduce_zero D h]
  · unfold reduce
    dsimp only
    rw [ite_eq_right (fun test => h (zero.mp test))]
    dsimp only
    rw [Input.reduce_positive D h]
    let q := (normalized D (totals D).1).1
    let k := (ceilings q).1
    have actual : q=D.normalized D.totals := by rw [show q=(normalized D (totals D).1).1 from rfl,normalized_value,totals_value]
    have count : k=Input.copyCounts (D.normalized D.totals) := by
      rw [show k=(ceilings q).1 from rfl,ceilings_value,actual]
    let pack (price : Vector Code m) (ks : Vector ℕ m) : Input.Result m :=
      .replicated price ks (materialize D ks) (D.totals.work+(materialize D ks).work+60*m+40)
    rw [show (totals D).1.work=D.totals.work from congrArg Input.Totals.work (totals_value D)]
    exact congrArg₂ pack actual count

def reductionBudget {R : Type*} [Semiring R] (m b : R) : R :=
  m*(3*BinaryRawRational.budget (aggregateWidth m b)+10)+1+
    16*(m*(2*b+1)+2)^2+4*(m*(2*b+1)+2)+8+
    (m*(2*BinaryRawRational.budget (m+b)+6)+8*m+4)+
    ((m+2)*BinaryRawRational.budget (normalizedWidth m b)+8*m+10)+
    (m*(BinaryRawRational.budget (normalizedWidth m b)+4)+8*m+4)

set_option maxHeartbeats 1000000 in
theorem reduce_paid {m b : ℕ} (D : Input m) (fits : InputFits D b) :
    (reduce D).2 ≤ reductionBudget m b := by
  let a := totals D
  let w := BinaryNaturalView.encode a.1.objective.num
  let z := BinaryArithmetic.isZero w.1
  let setup := a.2+w.2+z.2+8
  have hb := totals_paid D fits
  have hs : D.totals.weight.Bounded (m*(b+1)) ∧ D.totals.objective.Bounded (m*(2*b+1)) := by
    simpa only [Input.totals,List.length_finRange] using D.scan_bounded b fits.weights fits.costs (List.finRange m)
  have bits : a.1.objective.num.size ≤ m*(2*b+1)+1 := by
    rw [show a.1=D.totals from totals_value D]
    exact (Code.bounded_bits hs.2).1
  have wc : w.2 ≤ 16*(m*(2*b+1)+2)^2 :=
    (BinaryNaturalView.encode_paid a.1.objective.num).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have zw : w.1.length ≤ m*(2*b+1)+1 := by
    simp only [w,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]
    exact bits
  have zc := (BinaryArithmetic.isZero_spec w.1).2.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right zw 1))
  have zm := zeroMask_paid D fits
  have nc := normalized_paid D fits
  have cc : (ceilings (normalized D a.1).1).2 ≤ m*(BinaryRawRational.budget (normalizedWidth m b)+4)+8*m+4 := by
    apply ceilings_paid
    intro i
    rw [normalized_value,show a.1=D.totals from totals_value D]
    apply Code.bounded_mono (D.normalized_bounded b fits.weights fits.costs i)
    unfold normalizedWidth
    omega
  unfold reduce
  dsimp only
  unfold reductionBudget
  change a.2 ≤ _ at hb
  change z.2 ≤ _ at zc
  have next : (normalized D a.1).2 ≤ (m+2)*BinaryRawRational.budget (normalizedWidth m b)+8*m+10 := by
    rw [show a.1=D.totals from totals_value D]
    exact nc
  split
  · change setup+(zeroMask D).2 ≤ _
    unfold setup
    omega
  · change setup+(normalized D a.1).2+(ceilings (normalized D a.1).1).2 ≤ _
    unfold setup
    omega

end DirectedFlowCutGap.BinaryVertexReductionArithmetic
