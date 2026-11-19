import DirectedFlowCutGap.EncodedEdgeGadget
import DirectedFlowCutGap.ChargedEdgeDyadicLabels
import DirectedFlowCutGap.BinaryVertexReductionArithmetic

/-! The dyadic gadget with binary label tests, exact dyadic weight
materialization and measured sums of the input edge prices. -/

namespace DirectedFlowCutGap.BinaryEdgeGadget

open BinaryArithmetic BinaryRational RawNonnegativeRational EncodedEdgeGadget
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)

structure InputFits {n : ℕ} (D : Input n) (b : ℕ) : Prop where
  weights : ∀ u v : Fin n, D.weights[u.val][v.val].Bounded b
  costs : ∀ u v : Fin n, D.costs[u.val][v.val].Bounded b

def labels {n : ℕ} (D : Input n) : Labels n × ℕ :=
  batch fun u => batch fun v =>
    let q := BinaryRawRational.encode D.weights[u.val][v.val]
    let r := ChargedEdgeDyadicLabels.label n q.1
    (r.1,q.2+r.2+4)

@[simp] theorem labels_value {n : ℕ} (D : Input n) : (labels D).1=labelTable D := by
  simp only [labels,batch_value,labelTable,ChargedEdgeDyadicLabels.label_value,BinaryRawRational.encode_value]

def labelsBudget {R : Type*} [Semiring R] (n b : R) : R :=
  n*(n*(40*(b+2)^2+ChargedEdgeDyadicLabels.labelBudget n (b+1)+4)+8*n+4)+8*n+4

theorem labels_paid {n b : ℕ} (D : Input n) (fit : InputFits D b) : (labels D).2 ≤ labelsBudget n b := by
  unfold labels labelsBudget
  apply batch_paid
  intro u
  apply batch_paid
  intro v
  have w := fit.weights u v
  have e := BinaryRawRational.encode_paid w
  have r := ChargedEdgeDyadicLabels.label_paid n _ (BinaryRawRational.encode_width w)
  dsimp only
  omega

private def priceAt {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) : Code :=
  if x=EdgeToVertex.right (labelAt l) e ∨ x=EdgeToVertex.left (labelAt l) e
  then D.costs[e.1.val][e.2.val] else Code.zero

private theorem priceAt_value {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) :
    priceAt D l x e=edgeCharge D l x e := by
  have distinct : EdgeToVertex.right (labelAt l) e ≠ EdgeToVertex.left (labelAt l) e := by
    simp [EdgeToVertex.right,EdgeToVertex.left]
  by_cases r : x=EdgeToVertex.right (labelAt l) e
  · simp [priceAt,edgeCharge,r,distinct,Code.add,Code.zero]
  · by_cases h : x=EdgeToVertex.left (labelAt l) e
    · simp [priceAt,edgeCharge,h,Ne.symm distinct,Code.add,Code.zero]
    · simp [priceAt,edgeCharge,r,h,Code.add,Code.zero]

private theorem priceAt_fit {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (x : RawNode n) (e : Pair n) : (priceAt D l x e).Bounded b := by
  unfold priceAt
  split
  · exact fit.costs e.1 e.2
  · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)

private def priceFields {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) :
    List (Pair n) → List Fraction × ℕ
  | [] => ([],1)
  | e::es =>
    let a := BinaryRawRational.encode (priceAt D l x e)
    let rest := priceFields D l x es
    (a.1::rest.1,a.2+rest.2+64*(n+4))

private theorem priceFields_value {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (es : List (Pair n)) :
    (priceFields D l x es).1 = es.map (fun e => (BinaryRawRational.encode (priceAt D l x e)).1) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [priceFields, List.map_cons, ih]

private theorem priceFields_paid {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (x : RawNode n) (es : List (Pair n)) :
    (priceFields D l x es).2 ≤ es.length*(40*(b+2)^2+64*(n+4))+1 := by
  induction es with
  | nil => simp only [priceFields,List.length_nil,Nat.zero_mul,Nat.zero_add,le_rfl]
  | cons e es ih =>
    have a := BinaryRawRational.encode_paid (priceAt_fit D l fit x e)
    simp only [priceFields,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private def nodeCost {n : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n)) (x : RawNode n) : Code × ℕ :=
  let a := priceFields D l x es
  let b := BinaryFractionalRows.sum a.1
  let c := BinaryRawRational.decode b.1
  (c.1,a.2+b.2+c.2+4)

private theorem nodeCost_value {n : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n)) (x : RawNode n) :
    (nodeCost D l es x).1=FractionalCoverRawCore.sumCodes (es.map (edgeCharge D l x)) := by
  simp only [nodeCost,BinaryRawRational.decode_value,BinaryFractionalRows.sum_decode,priceFields_value,
    List.map_map,Function.comp_def,BinaryRawRational.encode_value,priceAt_value]

private def nodeCostBudget {R : Type*} [Semiring R] (n e b : R) : R :=
  let summation := e*(2048*((e+1)*(b+1+1)+1)^2+4)+1
  e*(40*(b+2)^2+64*(n+4))+1+summation+40*(e*(b+2)+2)^2+4

private theorem nodeCost_paid {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (es : List (Pair n)) (x : RawNode n) : (nodeCost D l es x).2 ≤ nodeCostBudget n es.length b := by
  let row := (priceFields D l x es).1
  have len : row.length=es.length := by simp only [row,priceFields_value,List.length_map]
  have bounded : ∀ q ∈ row, StoredBounded q (b+1) := by
    intro q mem
    rw [show row=(priceFields D l x es).1 from rfl,priceFields_value] at mem
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp mem
    exact BinaryRawRational.encode_width (priceAt_fit D l fit x e)
  have a := priceFields_paid D l fit x es
  have c := BinaryFractionalRows.sum_charge row (b+1) bounded
  rw [len] at c
  have size := BinaryFractionalRows.sum_stored_bound row (b+1)
    (fun q h => BinaryFractionalRows.stored_raw_bound (bounded q h))
  rw [len] at size
  have d := BinaryRawRational.decode_paid size
  change (BinaryRawRational.decode (BinaryFractionalRows.sum row).1).2 ≤ 40*(es.length*(b+2)+2)^2 at d
  change (priceFields D l x es).2+(BinaryFractionalRows.sum row).2+
    (BinaryRawRational.decode (BinaryFractionalRows.sum row).1).2+4 ≤ _
  simp only [nodeCostBudget]
  unfold BinaryFractionalRows.sumBound at c
  omega

private def weightField {n : ℕ} : RawNode n → Code × ℕ
  | .inr (_,_,some i) =>
    let q := BinaryRawRational.decode (ChargedEdgeDyadicLabels.powerFraction i.val)
    (q.1,q.2+8*(i.val+1)+8)
  | .inl _ | .inr (_,_,none) => (Code.zero,4)

private theorem weightField_value {n : ℕ} (x : RawNode n) : (weightField x).1=nodeWeight x := by
  rcases x with p | ⟨v,s,k⟩
  · rfl
  · cases k with
    | none => rfl
    | some i => simp only [weightField,nodeWeight,BinaryRawRational.decode_value,ChargedEdgeDyadicLabels.decode_power,
        EncodedEdgeLabels.valueCode]

private theorem depth_le (n : ℕ) : DyadicEdgeWeights.depth n ≤ n+1 :=
  Nat.add_le_add_right (Nat.log_le_self 2 n) 1

private def weightBudget {R : Type*} [Semiring R] (n : R) : R := 40*(n+3)^2+8*(n+2)+8

private theorem weightField_paid {n : ℕ} (x : RawNode n) : (weightField x).2 ≤ weightBudget n := by
  rcases x with p | ⟨v,s,k⟩
  · simp only [weightField,weightBudget]; omega
  · cases k with
    | none => simp only [weightField,weightBudget]; omega
    | some i =>
      have bound : i.val ≤ n+1 := (Nat.le_of_lt_succ i.isLt).trans (depth_le n)
      have work := BinaryRawRational.decode_paid (ChargedEdgeDyadicLabels.power_width i.val)
      have w := Nat.mul_le_mul_left 40 (Nat.pow_le_pow_left (show i.val+1+1 ≤ n+3 by omega) 2)
      simp only [weightField,weightBudget]
      omega

private def graphAllowance {R : Type*} [Semiring R] (n e m : R) : R :=
  192*(n+4)*(n^2+2*n*(n+4)*(e+1)+m*m+m+1)

def build {n : ℕ} (D : Input n) : Prepared D × ℕ :=
  let l := labels D
  let es := edges D
  let v := nodeVector D l.1
  let w := batch fun i => weightField v[i.val].val
  let c := batch fun i => nodeCost D l.1 es v[i.val].val
  (assemble D l.1 v w.1 c.1,l.2+w.2+c.2+graphAllowance n es.length v.size)

@[simp] theorem build_value {n : ℕ} (D : Input n) : (build D).1=EncodedEdgeGadget.build D := by
  let forLabels := fun l => buildWithLabels D l
  have h : (build D).1=forLabels (labels D).1 := by
    simp only [build,batch_value,weightField_value,nodeCost_value,forLabels,buildWithLabels]
  rw [h,labels_value]
  rfl

theorem edges_length {n : ℕ} (D : Input n) : (edges D).length ≤ n^2 := by
  unfold edges
  exact (List.length_filter_le _ _).trans_eq (by
    simpa only [List.length_finRange,pow_two,SProd.sprod,List.instSProd] using
      List.length_product (List.finRange n) (List.finRange n))

def dimension {R : Type*} [Semiring R] (n : R) : R := 2*n*(n+4)

theorem size_le {n : ℕ} (D : Input n) : (build D).1.size ≤ dimension n := by
  rw [build_value]
  exact (build_size_le D).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 n) 4))

def budget {R : Type*} [Semiring R] (n b : R) : R :=
  labelsBudget n b+(dimension n*weightBudget n+8*dimension n+4)+
    (dimension n*nodeCostBudget n (n^2) b+8*dimension n+4)+graphAllowance n (n^2) (dimension n)

theorem build_paid {n b : ℕ} (D : Input n) (fit : InputFits D b) : (build D).2 ≤ budget n b := by
  let es := edges D
  let v := nodeVector D (labels D).1
  have el : es.length ≤ n^2 := edges_length D
  have dim : v.size ≤ dimension n := size_le D
  have w := batch_paid (fun i => weightField v[i.val].val) (fun i => weightField_paid v[i.val].val)
  have c := batch_paid (fun i => nodeCost D (labels D).1 es v[i.val].val)
    (fun i => nodeCost_paid D (labels D).1 fit es v[i.val].val)
  have l := labels_paid D fit
  unfold budget
  change (labels D).2+(batch (fun i => weightField v[i.val].val)).2+
    (batch (fun i => nodeCost D (labels D).1 es v[i.val].val)).2+graphAllowance n es.length v.size ≤ _
  apply Nat.add_le_add (Nat.add_le_add (Nat.add_le_add l (w.trans ?_)) (c.trans ?_))
  · unfold graphAllowance
    gcongr
  · gcongr
  · simp only [nodeCostBudget]
    gcongr

theorem budget_mono {n m a b : ℕ} (h : n ≤ m) (w : a ≤ b) : budget n a ≤ budget m b := by
  simp only [budget,labelsBudget,ChargedEdgeDyadicLabels.labelBudget,ChargedEdgeDyadicLabels.checkBudget,
    nodeCostBudget,weightBudget,graphAllowance,dimension]
  gcongr

theorem budget_eval (n b : Polynomial ℕ) (x : ℕ) :
    (budget n b).eval x = budget (n.eval x) (b.eval x) := by
  simp only [budget,labelsBudget,ChargedEdgeDyadicLabels.labelBudget,ChargedEdgeDyadicLabels.checkBudget,
    nodeCostBudget,weightBudget,graphAllowance,dimension,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_one,Polynomial.eval_ofNat]

theorem fields_fit {n b : ℕ} (D : Input n) (fit : InputFits D b) :
    VertexReductionWidths.InputFits (build D).1.data (n^2*(b+1)+n+1) := by
  rw [build_value]
  constructor
  · intro i
    simp only [EncodedEdgeGadget.build,buildWithLabels,assemble,Vector.getElem_ofFn]
    have h := depth_le n
    apply Code.bounded_mono (a:=DyadicEdgeWeights.depth n)
    · rcases (nodeVector D (labelTable D))[i.val].val with p | ⟨u,s,l⟩
      · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)
      · exact EncodedEdgeLabels.valueCode_bounded l
    · omega
  · intro i
    simp only [EncodedEdgeGadget.build,buildWithLabels,assemble,Vector.getElem_ofFn]
    have raw (e : Pair n) : (edgeCharge D (labelTable D) (nodeVector D (labelTable D))[i.val].val e).Bounded b := by
      rw [← priceAt_value]
      exact priceAt_fit D (labelTable D) fit _ e
    apply Code.bounded_mono (FractionalCoverRawCore.sumCodes_bounded _ b ?_) ?_
    · intro q mem
      obtain ⟨e,_,rfl⟩ := List.mem_map.mp mem
      exact raw e
    · rw [List.length_map]
      have h := Nat.mul_le_mul_right (b+1) (edges_length D)
      omega

end DirectedFlowCutGap.BinaryEdgeGadget
