import DirectedFlowCutGap.BinaryEdgeFamilyArithmetic

/-! Retain one materialized price row per adaptive stage. The actual
price test and each update use binary arithmetic on that row. -/

namespace DirectedFlowCutGap.BinaryEdgeFamilyState

open scoped NNRat BigOperators
open BinaryArithmetic RawNonnegativeRational RandomizedEdgeFamily
open BinaryEdgeFamilyArithmetic
open RetainedGridState (PairFlags flag)
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)

structure State (n : ℕ) where
  prices : Row n
  cuts : List (Finset (Edge n))

def State.observe {n : ℕ} (s : State n) : RationalWeakFamily.History (Edge n) :=
  ⟨fun e => (read s.prices e).value,s.cuts⟩

def State.Canonical {n : ℕ} (s : State n) : Prop :=
  ∀ i : Fin (n*n), s.prices[i.val]=Code.ofNNRat s.prices[i.val].value

def initial (n : ℕ) : State n := ⟨Vector.replicate (n*n) Code.one,[]⟩

theorem initial_observe (n : ℕ) : (initial n).observe=(CheckedMWHistory.initial : RationalWeakFamily.History (Edge n)) := by
  simp only [initial,State.observe,BinaryEdgeFamilyArithmetic.read,Vector.getElem_replicate,Code.value_one,CheckedMWHistory.initial]

theorem initial_canonical (n : ℕ) : (initial n).Canonical := by
  intro i
  simp only [initial,Vector.getElem_replicate,Code.value_one]
  rfl

theorem initial_fit (n B : ℕ) : Fits (initial n).prices B := fun _ => by
  simpa only [initial,Vector.getElem_replicate] using Code.bounded_mono Code.bounded_one (Nat.zero_le B)

private def replacePrice (old factor : Code) (selected : Bool) : Code × ℕ :=
  if selected then
    let product := BinaryRawRational.mul old factor
    let canon := BinaryRationalNormalize.normalize product.1
    (canon.1,product.2+canon.2+4)
  else (old,4)

private theorem replacePrice_value (old factor : Code) (selected : Bool) :
    (replacePrice old factor selected).1.value=old.value*(if selected then factor.value else 1) := by
  cases selected <;> simp only [replacePrice,Bool.false_eq_true,BinaryRawRational.mul_value,
    BinaryRationalNormalize.normalize_value,ite_false,ite_true,Code.value_ofNNRat,Code.value_mul,mul_one]

private theorem replacePrice_canonical (old factor : Code) (selected : Bool) (canonical : old=Code.ofNNRat old.value) :
    (replacePrice old factor selected).1=Code.ofNNRat (replacePrice old factor selected).1.value := by
  cases selected
  · exact canonical
  · simp only [replacePrice,ite_true,BinaryRationalNormalize.normalize_value,Code.value_ofNNRat]

def advance {n : ℕ} (p : Preparation n) (s : State n) (mask : PairFlags n) : State n × ℕ :=
  let row := batch fun i =>
    let e : Edge n := finProdFinEquiv.symm i
    replacePrice s.prices[i.val] p.gain[i.val] (flag mask e)
  (⟨row.1,EncodedEdgeRounding.selectedEdges mask :: s.cuts⟩,row.2+64*(n+1)^4)

theorem advance_observe {n : ℕ} (D : Input n) (s : State n) (mask : PairFlags n) :
    (advance (prepare D).1 s mask).1.observe =
      CheckedMWHistory.advance (floored D) D.factor (scale n) s.observe (EncodedEdgeRounding.selectedEdges mask) := by
  have edge (e : Edge n) : e ∈ EncodedEdgeRounding.selectedEdges mask ↔ flag mask e=true := by
    simp only [EncodedEdgeRounding.selectedEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  unfold advance State.observe CheckedMWHistory.advance
  simp only [BinaryEdgeFamilyArithmetic.read,batch_value,Vector.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply,replacePrice_value]
  congr 1
  funext e
  have gain : (prepare D).1.gain[(finProdFinEquiv e).val].value =
      1+scale n/(floored D e*D.factor) := prepare_gain D e
  by_cases h : flag mask e=true
  · simp only [ite_eq_left h,ite_eq_left ((edge e).mpr h),gain]
  · simp only [ite_eq_right h,ite_eq_right (fun m => h ((edge e).mp m))]

theorem advance_canonical {n : ℕ} (p : Preparation n) (s : State n) (mask : PairFlags n) (h : s.Canonical) :
    (advance p s mask).1.Canonical := by
  intro i
  simp only [advance,batch_value,Vector.getElem_ofFn,Fin.eta]
  apply replacePrice_canonical
  exact h i

set_option maxHeartbeats 800000 in
private theorem replacePrice_fits {x g : Code} {B C : ℕ} (hx : x.Bounded B) (hg : g.Bounded C) (b : Bool) :
    (replacePrice x g b).1.Bounded (B+C) ∧
      (replacePrice x g b).2 ≤ BinaryRawRational.budget (B+C)+BinaryRationalNormalize.budget (B+C)+4 := by
  cases b
  · change x.Bounded (B+C) ∧ 4 ≤ _
    exact ⟨Code.bounded_mono hx (Nat.le_add_right _ _),Nat.le_add_left _ _⟩
  · let t := BinaryRawRational.mul x g
    have ht : t.1.Bounded (B+C) := by
      change (BinaryRawRational.mul x g).1.Bounded _
      rw [BinaryRawRational.mul_value]
      exact Code.bounded_mul hx hg
    have work : t.2 ≤ BinaryRawRational.budget (B+C) :=
      BinaryRawRational.mul_paid (Code.bounded_mono hx (Nat.le_add_right _ _)) (Code.bounded_mono hg (Nat.le_add_left _ _))
    change (BinaryRationalNormalize.normalize t.1).1.Bounded (B+C) ∧
      t.2+(BinaryRationalNormalize.normalize t.1).2+4 ≤ _
    exact ⟨BinaryRationalNormalize.normalize_width ht,
      Nat.add_le_add_right (Nat.add_le_add work (BinaryRationalNormalize.normalize_paid ht)) _⟩

def advanceBudget {R : Type*} [Semiring R] (n B C : R) : R :=
  n*n*(BinaryRawRational.budget (B+C)+BinaryRationalNormalize.budget (B+C)+4)+8*(n*n)+4+64*(n+1)^4

theorem advance_fits_paid {n B C : ℕ} (p : Preparation n) (s : State n) (mask : PairFlags n)
    (prices : Fits s.prices B) (gain : Fits p.gain C) :
    Fits (advance p s mask).1.prices (B+C) ∧ (advance p s mask).2 ≤ advanceBudget n B C := by
  let f : Fin (n*n) → Code × ℕ := fun i =>
    replacePrice s.prices[i.val] p.gain[i.val] (flag mask (finProdFinEquiv.symm i))
  have work (i : Fin (n*n)) := replacePrice_fits (prices i) (gain i) (flag mask (finProdFinEquiv.symm i))
  constructor
  · intro i
    change (batch f).1[i.val].Bounded (B+C)
    simp only [batch_value,Vector.getElem_ofFn,Fin.eta]
    exact (work i).1
  · exact Nat.add_le_add_right (batch_paid f fun i => (work i).2) _

private def zeroTest (q : Code) : Bool × ℕ :=
  let bytes := BinaryNaturalView.encode q.num
  let test := isZero bytes.1
  (test.1,bytes.2+test.2+4)

private theorem zeroTest_true (q : Code) : (zeroTest q).1=true ↔ q.value=0 := by
  change (isZero (BinaryNaturalView.encode q.num).1).1=true ↔ _
  rw [(isZero_spec _).1,BinaryNaturalView.encode_value,Code.value_eq_zero]

private theorem zeroTest_paid {q : Code} {B : ℕ} (hq : q.Bounded B) :
    (zeroTest q).2 ≤ 24*(B+2)^2 := by
  let bytes := BinaryNaturalView.encode q.num
  have fit := (Code.bounded_bits hq).1
  have len : bytes.1.length ≤ B+1 := by
    rw [show bytes.1=q.num.bits from BinaryNaturalView.encode_bits q.num,Nat.size_eq_bits_len]
    exact fit
  have rawWork := (BinaryNaturalView.encode_paid q.num).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right fit 1) 2))
  have test := (isZero_spec bytes.1).2.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right len 1))
  change bytes.2 ≤ 16*(B+2)^2 at rawWork
  change bytes.2+(isZero bytes.1).2+4 ≤ _
  nlinarith [Nat.zero_le (B*B)]

private def penalize (value weight alternative : Code) : Code × ℕ :=
  let test := zeroTest weight
  (if test.1 then alternative else value,test.2+4)

private theorem penalize_value (value weight alternative : Code) :
    (penalize value weight alternative).1=if 0<weight.value then value else alternative := by
  by_cases zero : weight.value=0
  · have h := (zeroTest_true _).mpr zero
    simp only [penalize,h,ite_true,zero,lt_irrefl,ite_false]
  · have h := fun eq => zero ((zeroTest_true weight).mp eq)
    have good : 0<weight.value := pos_iff_ne_zero.mpr zero
    simp only [penalize,ite_eq_right h,ite_eq_left good]

structure Query (n : ℕ) where
  input : EncodedEdgeLineInput.Input n
  limit : Code
  paid : ℕ

def query {n : ℕ} (D : Input n) (p : Preparation n) (demands : List (Edge n)) (s : State n) : Query n :=
  let t := sums p.adjusted s.prices
  let c := BinaryRawRational.mul p.factor t.1.objective
  let a := BinaryRawRational.add c.1 Code.one
  let banned := BinaryRationalNormalize.normalize a.1
  let row := batch fun i => penalize s.prices[i.val] p.adjusted[i.val] banned.1
  ⟨⟨D.adjacency,demands,Vector.ofFn fun u => Vector.ofFn fun v => read row.1 (u,v)⟩,c.1,
    t.2+c.2+a.2+banned.2+row.2+64*(n+1)^4⟩

theorem query_limit {n : ℕ} (D : Input n) (demands : List (Edge n)) (s : State n) :
    (query D (prepare D).1 demands s).limit.value=2*allowance D s.observe.costs := by
  simp only [query,BinaryRawRational.mul_value,Code.value_mul,prepare_factor,sums_objective,
    prepare_adjusted,State.observe,allowance]
  ring

theorem query_request {n : ℕ} (D : Input n) (s : State n) (canonical : s.Canonical) :
    (query D (prepare D).1 (RationalEdgeThresholds.demands D.adjacency D.weights) s).input =
      request D (RationalWeakFamily.penalizedCosts (adjusted D) D.factor s.observe.costs) := by
  let t := sums (prepare D).1.adjusted s.prices
  let c := BinaryRawRational.mul (prepare D).1.factor t.1.objective
  let a := BinaryRawRational.add c.1 Code.one
  let banned := BinaryRationalNormalize.normalize a.1
  have value : banned.1=Code.ofNNRat (D.factor*(∑ e, s.observe.costs e*adjusted D e)+1) := by
    simp only [banned,a,c,t,BinaryRationalNormalize.normalize_value,BinaryRawRational.add_value,Code.value_add,
      BinaryRawRational.mul_value,Code.value_mul,Code.value_one,prepare_factor,sums_objective,
      prepare_adjusted,State.observe]
  let prices := (query D (prepare D).1 (RationalEdgeThresholds.demands D.adjacency D.weights) s).input.costs
  have fields : prices = Vector.ofFn (fun u => Vector.ofFn fun v =>
      Code.ofNNRat (RationalWeakFamily.penalizedCosts (adjusted D) D.factor s.observe.costs (u,v))) := by
    apply Vector.ext
    intro u hu
    apply Vector.ext
    intro v hv
    let e : Edge n := (⟨u,hu⟩,⟨v,hv⟩)
    let i := finProdFinEquiv e
    simp only [prices,query,Vector.getElem_ofFn]
    change read (batch (fun j => penalize s.prices[j.val] (prepare D).1.adjusted[j.val] banned.1)).1 e =
      Code.ofNNRat (RationalWeakFamily.penalizedCosts (adjusted D) D.factor s.observe.costs e)
    simp only [BinaryEdgeFamilyArithmetic.read,batch_value,Vector.getElem_ofFn,penalize_value,State.observe,RationalWeakFamily.penalizedCosts]
    rw [show (prepare D).1.adjusted[i.val].value=adjusted D e from prepare_adjusted D e]
    by_cases h : 0<adjusted D e
    · rw [ite_eq_left h,ite_eq_left h]
      exact canonical i
    · rw [ite_eq_right h,ite_eq_right h]
      exact value
  unfold request
  exact congrArg (fun row => (⟨D.adjacency,RationalEdgeThresholds.demands D.adjacency D.weights,row⟩ :
    EncodedEdgeLineInput.Input n)) fields

private def maskWeights {n : ℕ} (D : EncodedEdgeLineInput.Input n) (mask : PairFlags n) : Row n :=
  Vector.ofFn fun i =>
    let e : Edge n := finProdFinEquiv.symm i
    if flag mask e && D.adjacency[e.1.val][e.2.val] then Code.one else Code.zero

private def flatten {n : ℕ} (D : EncodedEdgeLineInput.Input n) : Row n :=
  Vector.ofFn fun i =>
    let e : Edge n := finProdFinEquiv.symm i
    D.costs[e.1.val][e.2.val]

theorem cut_price {n : ℕ} (D : EncodedEdgeLineInput.Input n) (mask : PairFlags n) :
    (sums (maskWeights D mask) (flatten D)).1.objective.value =
      CheckedEdgeOracle.costQ D (EncodedEdgeRounding.selectedEdges mask) := by
  rw [sums_objective,CheckedEdgeOracle.costQ,EncodedEdgeRounding.selectedEdges,Finset.filter_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [BinaryEdgeFamilyArithmetic.read,flatten,maskWeights,Vector.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply,Bool.and_eq_true]
  split_ifs <;> simp only [Code.value_one,Code.value_zero,mul_one,mul_zero]

def check {n : ℕ} (q : Query n) : EncodedEdgeSolver.Output n → Option (PairFlags n) × ℕ
  | .cut mask =>
    let sum := sums (maskWeights q.input mask) (flatten q.input)
    let test := BinaryRawRational.le sum.1.objective q.limit
    (if test.1 then some mask else none,sum.2+test.2+64*(n+1)^4)
  | .infeasible _ | .invalid => (none,4)

theorem check_value {n : ℕ} (q : Query n) (B : ℚ≥0) (limit : q.limit.value=2*B)
    (out : EncodedEdgeSolver.Output n) :
    (check q out).1.map EncodedEdgeRounding.selectedEdges=CheckedEdgeOracle.check q.input B out := by
  cases out with
  | infeasible _ | invalid => rfl
  | cut mask =>
    let sum := sums (maskWeights q.input mask) (flatten q.input)
    have h : (BinaryRawRational.le sum.1.objective q.limit).1=true ↔
        CheckedEdgeOracle.costQ q.input (EncodedEdgeRounding.selectedEdges mask) ≤ 2*B := by
      rw [BinaryRawRational.le_value,Code.le_eq_true,limit,cut_price]
    change (if (BinaryRawRational.le sum.1.objective q.limit).1 then some mask else none).map
      EncodedEdgeRounding.selectedEdges = _
    unfold CheckedEdgeOracle.check
    dsimp only
    by_cases good : CheckedEdgeOracle.costQ q.input (EncodedEdgeRounding.selectedEdges mask) ≤ 2*B
    · rw [ite_eq_left (h.mpr good),ite_eq_left good]
      rfl
    · rw [ite_eq_right (fun eq => good (h.mp eq)),ite_eq_right good]
      rfl

def queryWidth {R : Type*} [Semiring R] (n B : R) : R := B+n*n*(2*B+1)+1

structure QueryFits {n : ℕ} (q : Query n) (B : ℕ) : Prop where
  prices : ∀ u v : Fin n, q.input.costs[u.val][v.val].Bounded B
  limit : q.limit.Bounded B

def queryBudget {R : Type*} [Semiring R] (n B : R) : R :=
  let W := queryWidth n B
  sumBudget n B+2*BinaryRawRational.budget W+BinaryRationalNormalize.budget W+
    (n*n*(24*(B+2)^2+4)+8*(n*n)+4)+64*(n+1)^4

set_option maxHeartbeats 1200000 in
theorem query_fits_paid {n B : ℕ} (D : Input n) (p : Preparation n) (d : List (Edge n)) (s : State n)
    (w : Fits p.adjusted B) (a : p.factor.Bounded B) (c : Fits s.prices B) :
    QueryFits (query D p d s) (queryWidth n B) ∧ (query D p d s).paid ≤ queryBudget n B := by
  let W := queryWidth n B
  let t := sums p.adjusted s.prices
  let limit := BinaryRawRational.mul p.factor t.1.objective
  let more := BinaryRawRational.add limit.1 Code.one
  let ban := BinaryRationalNormalize.normalize more.1
  let row := batch fun i => penalize s.prices[i.val] p.adjusted[i.val] ban.1
  have bW : B ≤ W := by unfold W queryWidth; omega
  have tw : t.1.objective.Bounded (n*n*(2*B+1)) := (sums_bounds p.adjusted s.prices w c).2
  have l : limit.1.Bounded (B+n*n*(2*B+1)) := by
    change (BinaryRawRational.mul p.factor t.1.objective).1.Bounded _
    rw [BinaryRawRational.mul_value]
    exact Code.bounded_mul a tw
  have lW : limit.1.Bounded W := Code.bounded_mono l (Nat.le_succ _)
  have m : more.1.Bounded W := by
    change (BinaryRawRational.add limit.1 Code.one).1.Bounded _
    rw [BinaryRawRational.add_value]
    simpa only [W,queryWidth,Nat.add_zero] using Code.bounded_add l Code.bounded_one
  have bn : ban.1.Bounded W := BinaryRationalNormalize.normalize_width m
  have cols (u v : Fin n) : (BinaryEdgeFamilyArithmetic.read row.1 (u,v)).Bounded W := by
    let i := finProdFinEquiv (u,v)
    simp only [BinaryEdgeFamilyArithmetic.read,row,batch_value,Vector.getElem_ofFn,penalize_value]
    split
    · exact Code.bounded_mono (c i) bW
    · exact bn
  constructor
  · refine ⟨?_,lW⟩
    intro u v
    simp only [query,Vector.getElem_ofFn]
    exact cols u v
  · have T : t.2 ≤ sumBudget n B := sums_paid p.adjusted s.prices w c
    have L : limit.2 ≤ BinaryRawRational.budget W := BinaryRawRational.mul_paid (Code.bounded_mono a bW)
      (Code.bounded_mono tw (by unfold W queryWidth; omega))
    have M : more.2 ≤ BinaryRawRational.budget W := BinaryRawRational.add_paid lW
      (Code.bounded_mono Code.bounded_one (Nat.zero_le _))
    have P : ban.2 ≤ BinaryRationalNormalize.budget W := BinaryRationalNormalize.normalize_paid m
    have rows := batch_paid (fun i => penalize s.prices[i.val] p.adjusted[i.val] ban.1)
      (fun i => Nat.add_le_add_right (zeroTest_paid (w i)) 4)
    change row.2 ≤ _ at rows
    change t.2+limit.2+more.2+ban.2+row.2+64*(n+1)^4 ≤
      sumBudget n B+2*BinaryRawRational.budget W+BinaryRationalNormalize.budget W+
        (n*n*(24*(B+2)^2+4)+8*(n*n)+4)+64*(n+1)^4
    omega

def checkBudget {R : Type*} [Semiring R] (n B : R) : R :=
  sumBudget n B+BinaryRawRational.budget (queryWidth n B)+64*(n+1)^4+4

theorem check_paid {n B : ℕ} (q : Query n) (fits : QueryFits q B) (out : EncodedEdgeSolver.Output n) :
    (check q out).2 ≤ checkBudget n B := by
  cases out with
  | invalid | infeasible _ => exact Nat.le_add_left _ _
  | cut mask =>
    let row := maskWeights q.input mask
    let prices := flatten q.input
    let sum := sums row prices
    have head : Fits row B := by
      intro i
      simp only [row,maskWeights,Vector.getElem_ofFn]
      split
      · exact Code.bounded_mono Code.bounded_one (Nat.zero_le _)
      · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)
    have values : Fits prices B := by
      intro i
      simp only [prices,flatten,Vector.getElem_ofFn]
      exact fits.prices (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
    have sized : sum.1.objective.Bounded (n*n*(2*B+1)) := (sums_bounds row prices head values).2
    have sumPaid : sum.2 ≤ sumBudget n B := sums_paid row prices head values
    have b1 : n*n*(2*B+1) ≤ queryWidth n B := by unfold queryWidth; omega
    have b2 : B ≤ queryWidth n B := by unfold queryWidth; omega
    have cmp := BinaryRawRational.le_paid (Code.bounded_mono sized b1) (Code.bounded_mono fits.limit b2)
    change sum.2+(BinaryRawRational.le sum.1.objective q.limit).2+64*(n+1)^4 ≤ _
    unfold checkBudget
    omega

end DirectedFlowCutGap.BinaryEdgeFamilyState
