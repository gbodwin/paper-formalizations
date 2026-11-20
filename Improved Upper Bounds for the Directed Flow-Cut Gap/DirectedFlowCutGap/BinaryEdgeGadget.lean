import DirectedFlowCutGap.EncodedEdgeGadget
import DirectedFlowCutGap.ChargedEdgeDyadicLabels
import DirectedFlowCutGap.BinaryVertexReductionArithmetic
import DirectedFlowCutGap.BinaryNaturalView
import DirectedFlowCutGap.BinaryVectorAccess
import DirectedFlowCutGap.BinaryShortScan

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

private theorem depth_le (n : ℕ) : DyadicEdgeWeights.depth n ≤ n+1 :=
  Nat.add_le_add_right (Nat.log_le_self 2 n) 1

private def equalNatural (a b : ℕ) : Bool × ℕ :=
  let x := BinaryNaturalView.encode a
  let y := BinaryNaturalView.encode b
  let result := BinaryArithmetic.compare x.1 y.1
  (result.equal,x.2+y.2+result.steps+4)

private theorem equalNatural_value (a b : ℕ) : (equalNatural a b).1=true ↔ a=b := by
  simp only [equalNatural,(compare_spec ..).2.1,BinaryNaturalView.encode_value]

private theorem equalNatural_paid {a b bound : ℕ} (aa : a ≤ bound) (bb : b ≤ bound) :
    (equalNatural a b).2 ≤ 64*(bound+1)^2 := by
  have aw := (BinaryNaturalOperations.size_le_self a).trans aa
  have bw := (BinaryNaturalOperations.size_le_self b).trans bb
  have x := (BinaryNaturalView.encode_paid a).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right aw 1) 2))
  have y := (BinaryNaturalView.encode_paid b).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right bw 1) 2))
  have size (k : ℕ) : (BinaryNaturalView.encode k).1.length=k.size := by
    rw [BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]
  have c := (compare_spec (BinaryNaturalView.encode a).1 (BinaryNaturalView.encode b).1).2.2
  rw [size,size] at c
  have c' := c.trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le aw bw) 1))
  unfold equalNatural
  dsimp only
  nlinarith only [x,y,c']

def equalFin {m : ℕ} (a b : Fin m) : Bool × ℕ := equalNatural a.val b.val

theorem equalFin_value {m : ℕ} (a b : Fin m) : (equalFin a b).1=true ↔ a=b := by
  rw [equalFin,equalNatural_value,Fin.val_inj]

theorem equalFin_paid {m : ℕ} (a b : Fin m) : (equalFin a b).2 ≤ 64*(m+1)^2 :=
  equalNatural_paid a.isLt.le b.isLt.le

private def equalLabel {n : ℕ} : DyadicEdgeWeights.Label n → DyadicEdgeWeights.Label n → Bool × ℕ
  | none,none => (true,2)
  | some i,some j => let r := equalFin i j; (r.1,r.2+2)
  | _,_ => (false,2)

private theorem equalLabel_value {n : ℕ} (a b : DyadicEdgeWeights.Label n) :
    (equalLabel a b).1=true ↔ a=b := by
  cases a <;> cases b <;> simp [equalLabel,equalFin_value]

private theorem equalLabel_paid {n : ℕ} (a b : DyadicEdgeWeights.Label n) :
    (equalLabel a b).2 ≤ 64*(n+2)^2+2 := by
  cases a <;> cases b <;> try simp [equalLabel]
  case some.some i j =>
    have hi := (Nat.lt_succ_iff.mp i.isLt).trans (depth_le n)
    have hj := (Nat.lt_succ_iff.mp j.isLt).trans (depth_le n)
    exact equalNatural_paid hi hj

def incidentWithControl {n : ℕ} (l : Labels n) (e : Pair n) : RawNode n → (Bool × ℕ) × ℕ
  | .inl _ => ((false,2),0)
  | .inr (u,side,i) =>
    let v := if side then e.1 else e.2
    let base := equalFin u v
    if base.1 then
      let edge := BinaryVectorAccess.readMatrix l e.1 e.2
      let label := equalLabel i edge.1
      ((label.1,base.2+label.2+8),edge.2)
    else ((false,base.2+6),0)

def incident {n : ℕ} (l : Labels n) (e : Pair n) (x : RawNode n) : Bool × ℕ :=
  (incidentWithControl l e x).1

theorem incident_reference {n : ℕ} (l : Labels n) (e : Pair n) (x : RawNode n) :
    incident l e x = match x with
      | .inl _ => (false,2)
      | .inr (u,side,i) =>
        let v := if side then e.1 else e.2
        let base := equalFin u v
        if base.1 then
          let label := equalLabel i (labelAt l e)
          (label.1,base.2+label.2+8)
        else (false,base.2+6) := by
  rcases x with port | ⟨u,side,i⟩
  · rfl
  · cases side <;> simp only [incident,incidentWithControl,BinaryVectorAccess.readMatrix_value,labelAt,
      Bool.false_eq_true,ite_false,ite_true] <;> split <;> rfl

theorem incident_control_paid {n width : ℕ} (l : Labels n) (e : Pair n) (x : RawNode n)
    (fits : n.size ≤ width) : (incidentWithControl l e x).2 ≤ 2*BinaryVectorAccess.budget width := by
  rcases x with port | ⟨u,side,i⟩
  · exact Nat.zero_le _
  · cases side <;> simp only [incidentWithControl,Bool.false_eq_true,ite_false,ite_true] <;>
      split <;> first | exact BinaryVectorAccess.readMatrix_paid l e.1 e.2 fits fits | exact Nat.zero_le _

theorem incident_iff {n : ℕ} (l : Labels n) (e : Pair n) (x : RawNode n) :
    (incident l e x).1=true ↔ x=EdgeToVertex.right (labelAt l) e ∨ x=EdgeToVertex.left (labelAt l) e := by
  rcases x with pair | ⟨u,b,i⟩
  · simp [incident_reference,EdgeToVertex.right,EdgeToVertex.left]
  · cases b <;> simp only [incident_reference,EdgeToVertex.right,EdgeToVertex.left, Bool.false_eq_true,
      ite_false,ite_true,Sum.inr.injEq,Prod.mk.injEq,false_and,true_and,and_false,false_or] <;>
    split <;> simp_all [equalFin_value,equalLabel_value]

def incidentBudget {R : Type*} [Semiring R] (n : R) : R := 128*(n+2)^2+10

theorem incident_paid {n : ℕ} (l : Labels n) (e : Pair n) (x : RawNode n) :
    (incident l e x).2 ≤ incidentBudget n := by
  rw [incident_reference]
  rcases x with pair | ⟨u,b,i⟩
  · simp [incidentBudget]
  · let v := if b then e.1 else e.2
    have base : (equalFin u v).2 ≤ 64*(n+2)^2 := equalNatural_paid
      (u.isLt.le.trans (Nat.le_succ n)) (v.isLt.le.trans (Nat.le_succ n))
    have label := equalLabel_paid i (labelAt l e)
    change (if (equalFin u v).1 then ((equalLabel i (labelAt l e)).1,
      (equalFin u v).2+(equalLabel i (labelAt l e)).2+8) else (false,(equalFin u v).2+6)).2 ≤ _
    unfold incidentBudget
    split <;> omega

private def incidentTest {n : ℕ} (l : Labels n) (x : RawNode n) (e : Pair n) : (Bool × ℕ) × ℕ :=
  let r := incidentWithControl l e x
  ((r.1.1,r.1.2+4),r.2)

private def incidentLoopWithControl {n : ℕ} (l : Labels n) (x : RawNode n) (paid : ℕ) (es : List (Pair n)) :
    (Bool × ℕ) × ℕ := BinaryShortScan.run (incidentTest l x) paid es

private def incidentLoop {n : ℕ} (l : Labels n) (x : RawNode n) (paid : ℕ) (es : List (Pair n)) : Bool × ℕ :=
  (incidentLoopWithControl l x paid es).1

private theorem incidentLoop_reference {n : ℕ} (l : Labels n) (x : RawNode n) (paid : ℕ) (es : List (Pair n)) :
    incidentLoop l x paid es=BinaryShortScan.reference (fun e => let r := incident l e x; (r.1,r.2+4)) paid es := by
  simp only [incidentLoop,incidentLoopWithControl,BinaryShortScan.run_reference]
  rfl

private theorem incidentLoop_iff {n : ℕ} (l : Labels n) (x : RawNode n) (paid : ℕ) (es : List (Pair n)) :
    (incidentLoop l x paid es).1=true ↔ ∃ e ∈ es, x=EdgeToVertex.right (labelAt l) e ∨ x=EdgeToVertex.left (labelAt l) e := by
  simp only [incidentLoop_reference,BinaryShortScan.reference_true,incident_iff]

private theorem incidentLoop_paid {n : ℕ} (l : Labels n) (x : RawNode n) (paid : ℕ) (es : List (Pair n)) :
    (incidentLoop l x paid es).2 ≤ paid+es.length*(incidentBudget n+4)+1 := by
  rw [incidentLoop_reference]
  exact BinaryShortScan.reference_paid _ _ _ _ (fun e _ => Nat.add_le_add_right (incident_paid l e x) 4)

private theorem incidentLoop_control_paid {n : ℕ} (l : Labels n) (x : RawNode n) (paid : ℕ) (es : List (Pair n)) :
    (incidentLoopWithControl l x paid es).2 ≤
      BinaryShortScan.controlBudget es.length paid (incidentBudget n+4) (2*BinaryVectorAccess.budget n) :=
  BinaryShortScan.run_paid _ _ _ _ _ (fun e _ => ⟨Nat.add_le_add_right (incident_paid l e x) 4,
    incident_control_paid l e x (BinaryNaturalOperations.size_le_self n)⟩)

private def keepLabel {n : ℕ} (l : Labels n) (es : List (Pair n)) : RawNode n → Bool × ℕ
  | .inl _ => (true,2)
  | .inr x => incidentLoop l (.inr x) 0 es

private theorem keepLabel_iff {n : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n))
    (correct : es=edges D) (x : RawNode n) : (keepLabel l es x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x := by
  subst es
  rcases x with ⟨u,side⟩ | x
  · simp only [keepLabel,true_iff]
    exact Or.inl ⟨u,side,rfl⟩
  · simp only [keepLabel,incidentLoop_iff,EdgeToVertex.Active,Sum.inr_ne_inl,exists_false,false_or,edges_mem]

private theorem keepLabel_paid {n : ℕ} (l : Labels n) (es : List (Pair n)) (x : RawNode n) :
    (keepLabel l es x).2 ≤ es.length*(incidentBudget n+4)+2 := by
  rcases x with x | x
  · simp [keepLabel]
  · exact (incidentLoop_paid l (.inr x) 0 es).trans (by omega)

private def priceAt {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) : Code × ℕ :=
  let r := incident l e x
  (if r.1 then D.costs[e.1.val][e.2.val] else Code.zero,r.2+4)

private theorem priceAt_value {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) :
    (priceAt D l x e).1=edgeCharge D l x e := by
  have distinct : EdgeToVertex.right (labelAt l) e ≠ EdgeToVertex.left (labelAt l) e := by
    simp [EdgeToVertex.right,EdgeToVertex.left]
  by_cases r : x=EdgeToVertex.right (labelAt l) e
  · simp [priceAt,incident_iff,edgeCharge,r,distinct,Code.add,Code.zero]
  · by_cases h : x=EdgeToVertex.left (labelAt l) e
    · simp [priceAt,incident_iff,edgeCharge,h,Ne.symm distinct,Code.add,Code.zero]
    · simp [priceAt,incident_iff,edgeCharge,r,h,Code.add,Code.zero]

private theorem priceAt_fit {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (x : RawNode n) (e : Pair n) : (priceAt D l x e).1.Bounded b := by
  dsimp only [priceAt]
  split
  · exact fit.costs e.1 e.2
  · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)

private def priceFields {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) :
    List (Pair n) → List Fraction × ℕ
  | [] => ([],1)
  | e::es =>
    let c := priceAt D l x e
    let a := BinaryRawRational.encode c.1
    let rest := priceFields D l x es
    (a.1::rest.1,c.2+a.2+rest.2+4)

private theorem priceFields_value {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (es : List (Pair n)) :
    (priceFields D l x es).1 = es.map (fun e => (BinaryRawRational.encode (priceAt D l x e).1).1) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [priceFields, List.map_cons, ih]

private theorem priceFields_paid {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (x : RawNode n) (es : List (Pair n)) :
    (priceFields D l x es).2 ≤ es.length*(40*(b+2)^2+incidentBudget n+8)+1 := by
  induction es with
  | nil => simp only [priceFields,List.length_nil,Nat.zero_mul,Nat.zero_add,le_rfl]
  | cons e es ih =>
    have a := BinaryRawRational.encode_paid (priceAt_fit D l fit x e)
    have c := incident_paid l e x
    change (incident l e x).2+4+
      (BinaryRawRational.encode (priceAt D l x e).1).2+(priceFields D l x es).2+4 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
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
  e*(40*(b+2)^2+incidentBudget n+8)+1+summation+40*(e*(b+2)+2)^2+4

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

private def adjacencyCell {n : ℕ} (D : Input n) (labels : Labels n) :
    RawNode n → RawNode n → Bool × ℕ
  | .inl (u,true), .inl (v,false) => equalFin u v
  | .inl (u,true), .inr (v,true,_) => equalFin u v
  | .inr (u,false,_), .inl (v,false) => equalFin u v
  | .inr (u,false,_), .inr (v,true,_) => equalFin u v
  | .inr (u,true,i), .inr (v,false,j) =>
    if D.adjacency[u.val][v.val] then
      let label := labelAt labels (u,v)
      let a := equalLabel label i
      let b := equalLabel label j
      (a.1 && b.1,a.2+b.2+8)
    else (false,4)
  | _,_ => (false,2)

private theorem adjacencyCell_iff {n : ℕ} (D : Input n) (labels : Labels n) (x y : RawNode n) :
    (adjacencyCell D labels x y).1=true ↔ EdgeToVertex.RawAdj D.graph (labelAt labels) x y := by
  rcases x with ⟨u,b⟩ | ⟨u,b,i⟩ <;> rcases y with ⟨v,c⟩ | ⟨v,c,j⟩ <;>
    cases b <;> cases c <;>
    simp [adjacencyCell,EdgeToVertex.RawAdj,Input.graph,equalFin_value]
  split <;> simp_all [equalLabel_value]

private def adjacencyCellBudget {R : Type*} [Semiring R] (n : R) : R := 128*(n+2)^2+12

private theorem adjacencyCell_paid {n : ℕ} (D : Input n) (labels : Labels n) (x y : RawNode n) :
    (adjacencyCell D labels x y).2 ≤ adjacencyCellBudget n := by
  rcases x with ⟨u,b⟩ | ⟨u,b,i⟩ <;> rcases y with ⟨v,c⟩ | ⟨v,c,j⟩ <;>
    have same : (equalNatural u.val v.val).2 ≤ 64*(n+2)^2 :=
      equalNatural_paid (u.isLt.le.trans (Nat.le_succ n)) (v.isLt.le.trans (Nat.le_succ n)) <;>
    cases b <;> cases c <;> simp only [adjacencyCell,adjacencyCellBudget,equalFin] <;> try omega
  split
  · have a := equalLabel_paid (labelAt labels (u,v)) i
    have b := equalLabel_paid (labelAt labels (u,v)) j
    omega
  · omega

private def adjacencyMatrix {n m : ℕ} (D : Input n) (l : Labels n) (v : Vector (Node D l) m) :
    Vector (Vector Bool m) m × ℕ :=
  batch fun i => batch fun j => adjacencyCell D l v[i.val].val v[j.val].val

private theorem adjacencyMatrix_value {n : ℕ} (D : Input n) :
    (adjacencyMatrix D (labelTable D) (nodeVector D (labelTable D))).1=
      (EncodedEdgeGadget.build D).data.adjacency := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [adjacencyMatrix,batch_value,Vector.getElem_ofFn]
  apply Bool.eq_iff_iff.mpr
  rw [adjacencyCell_iff]
  exact (build_adj D ⟨i,hi⟩ ⟨j,hj⟩).symm

private def adjacencyBudget {R : Type*} [Semiring R] (n m : R) : R :=
  m*(m*adjacencyCellBudget n+8*m+4)+8*m+4

private theorem adjacencyMatrix_paid {n m : ℕ} (D : Input n) (l : Labels n)
    (v : Vector (Node D l) m) : (adjacencyMatrix D l v).2 ≤ adjacencyBudget n m := by
  unfold adjacencyMatrix adjacencyBudget
  apply batch_paid
  intro i
  exact batch_paid _ (fun j => adjacencyCell_paid D l v[i.val].val v[j.val].val)

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

def build {n : ℕ} (D : Input n) : Prepared D × ℕ :=
  let l := labels D
  let es := edgesWithCost D
  let nodes := nodeVectorWithCost D l.1 (keepLabel l.1 es.1) (keepLabel_iff D l.1 es.1 (edgesWithCost_value D))
  let v := nodes.1
  let a := adjacencyMatrix D l.1 v
  let w := batch fun i => weightField v[i.val].val
  let c := batch fun i => nodeCost D l.1 es.1 v[i.val].val
  (⟨v.size,l.1,v,⟨a.1,w.1,c.1⟩⟩,l.2+w.2+c.2+a.2+es.2+nodes.2+8)

@[simp] theorem build_value {n : ℕ} (D : Input n) : (build D).1=EncodedEdgeGadget.build D := by
  let output (l : Labels n) : Prepared D :=
    let v := nodeVector D l
    ⟨v.size,l,v,⟨(adjacencyMatrix D l v).1,
      Vector.ofFn fun i => nodeWeight v[i.val].val,
      Vector.ofFn fun i => FractionalCoverRawCore.sumCodes ((edges D).map (edgeCharge D l v[i.val].val))⟩⟩
  have h : (build D).1=output (labels D).1 := by
    simp only [build,nodeVectorWithCost_value,edgesWithCost_value,batch_value,weightField_value,nodeCost_value,output]
  rw [h,labels_value]
  simp only [output,adjacencyMatrix_value]
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
    (dimension n*nodeCostBudget n (n^2) b+8*dimension n+4)+adjacencyBudget n (dimension n)+
    edgesBudget n+nodeVectorBudget n (n^2*(incidentBudget n+4)+2)+8

set_option maxHeartbeats 1000000 in
theorem build_paid {n b : ℕ} (D : Input n) (fit : InputFits D b) : (build D).2 ≤ budget n b := by
  let es := edgesWithCost D
  let test := keepLabel (labels D).1 es.1
  let correct := keepLabel_iff D (labels D).1 es.1 (edgesWithCost_value D)
  let nodes := nodeVectorWithCost D (labels D).1 test correct
  let m := (EncodedEdgeGadget.nodes D (labels D).1).length
  let v : Vector (Node D (labels D).1) m := nodes.1
  have el : es.1.length ≤ n^2 := by simpa only [es,edgesWithCost_value] using edges_length D
  have dim : m ≤ dimension n := size_le D
  have w := batch_paid (fun i : Fin m => weightField (v.get i).val) (fun i => weightField_paid (v.get i).val)
  have c := batch_paid (fun i : Fin m => nodeCost D (labels D).1 es.1 (v.get i).val)
    (fun i => nodeCost_paid D (labels D).1 fit es.1 (v.get i).val)
  have l := labels_paid D fit
  have a := adjacencyMatrix_paid D (labels D).1 v
  have e := edgesWithCost_paid D
  have g := nodeVectorWithCost_paid D (labels D).1 test correct _ (keepLabel_paid (labels D).1 es.1)
  have loops := Nat.mul_le_mul_left 8 dim
  have weightWork := Nat.mul_le_mul_right (weightBudget n) dim
  have costWork : nodeCostBudget n es.1.length b ≤ nodeCostBudget n (n^2) b := by
    simp only [nodeCostBudget]
    gcongr
  have limitsW := w.trans (Nat.add_le_add_right (Nat.add_le_add weightWork loops) 4)
  have limitsC := c.trans (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul dim costWork) loops) 4)
  have matrixWork : adjacencyBudget n m ≤ adjacencyBudget n (dimension n) := by
    unfold adjacencyBudget
    gcongr
  have limitsA := a.trans matrixWork
  have limitsG : nodes.2 ≤ nodeVectorBudget n (n^2*(incidentBudget n+4)+2) :=
    g.trans (by unfold nodeVectorBudget; gcongr)
  unfold budget
  have throughMatrix := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add l limitsW) limitsC) limitsA
  have throughEdges := Nat.add_le_add throughMatrix e
  exact Nat.add_le_add_right (Nat.add_le_add throughEdges limitsG) 8

theorem budget_mono {n m a b : ℕ} (h : n ≤ m) (w : a ≤ b) : budget n a ≤ budget m b := by
  simp only [budget,labelsBudget,ChargedEdgeDyadicLabels.labelBudget,ChargedEdgeDyadicLabels.checkBudget,
    nodeCostBudget,weightBudget,edgesBudget,nodeVectorBudget,incidentBudget,adjacencyBudget,adjacencyCellBudget,dimension]
  gcongr

theorem budget_eval (n b : Polynomial ℕ) (x : ℕ) :
    (budget n b).eval x = budget (n.eval x) (b.eval x) := by
  simp only [budget,labelsBudget,ChargedEdgeDyadicLabels.labelBudget,ChargedEdgeDyadicLabels.checkBudget,
    nodeCostBudget,weightBudget,edgesBudget,nodeVectorBudget,incidentBudget,adjacencyBudget,adjacencyCellBudget,dimension,
    Polynomial.eval_add,Polynomial.eval_mul,
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
