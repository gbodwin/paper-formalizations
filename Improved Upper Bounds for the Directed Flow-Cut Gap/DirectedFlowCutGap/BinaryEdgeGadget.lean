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

private def matrixWithControl {A : Type} {m : ℕ} (f : Fin m → Fin m → (A × ℕ) × ℕ) :
    (Vector (Vector A m) m × ℕ) × ℕ :=
  BinaryArrayBatch.runWithChildWork fun i => BinaryArrayBatch.runWithChildWork (f i)

private theorem matrix_reference {A : Type} {m : ℕ} (f : Fin m → Fin m → (A × ℕ) × ℕ) :
    (matrixWithControl f).1=batch (fun i => batch fun j => (f i j).1) := by
  unfold matrixWithControl
  rw [BinaryArrayBatch.child_projection]
  change batch _=batch _
  congr 1
  funext i
  exact BinaryArrayBatch.child_projection (f i)

private def matrixControlBudget {R : Type*} [Semiring R] (m cap child : R) : R :=
  BinaryArrayBatch.childCeiling m (m*cap+8*m+4) (BinaryArrayBatch.childCeiling m cap child)

private theorem matrix_paid {A : Type} {m cap child : ℕ} (f : Fin m → Fin m → (A × ℕ) × ℕ)
    (legacy : ∀ i j, (f i j).1.2≤cap) (extra : ∀ i j, (f i j).2≤child) :
    (matrixWithControl f).2 ≤ matrixControlBudget m cap child := by
  have rowFee (i : Fin m) : (BinaryArrayBatch.runWithChildWork (f i)).1.2 ≤ m*cap+8*m+4 := by
    rw [BinaryArrayBatch.child_projection]
    exact batch_paid _ (legacy i)
  have rowWork (i : Fin m) : (BinaryArrayBatch.runWithChildWork (f i)).2≤BinaryArrayBatch.childCeiling m cap child :=
    (BinaryArrayBatch.runWithChildWork_paid _ (legacy i) (extra i)).trans (BinaryArrayBatch.childBudget_le ..)
  exact (BinaryArrayBatch.runWithChildWork_paid _ rowFee rowWork).trans (BinaryArrayBatch.childBudget_le ..)

private def labelCell {n : ℕ} (D : Input n) (u v : Fin n) : (DyadicEdgeWeights.Label n × ℕ) × ℕ :=
  let stored := BinaryVectorAccess.readMatrix D.weights u v
  let q := BinaryRawRational.encode stored.1
  let r := ChargedEdgeDyadicLabels.label n q.1
  ((r.1,q.2+r.2+4),stored.2)

def labelsWithControl {n : ℕ} (D : Input n) : (Labels n × ℕ) × ℕ := matrixWithControl (labelCell D)

def labels {n : ℕ} (D : Input n) : Labels n × ℕ := (labelsWithControl D).1

theorem labels_reference {n : ℕ} (D : Input n) : labels D = batch (fun u => batch fun v =>
    let q := BinaryRawRational.encode D.weights[u.val][v.val]
    let r := ChargedEdgeDyadicLabels.label n q.1
    (r.1,q.2+r.2+4)) := by
  simp only [labels,labelsWithControl,matrix_reference,labelCell,BinaryVectorAccess.readMatrix_value]

private def labelCellBudget {R : Type*} [Semiring R] (n b : R) : R :=
  40*(b+2)^2+ChargedEdgeDyadicLabels.labelBudget n (b+1)+4

private theorem labelCell_paid {n b : ℕ} (D : Input n) (fit : InputFits D b) (u v : Fin n) :
    (labelCell D u v).1.2 ≤ labelCellBudget n b := by
  have w := fit.weights u v
  have e := BinaryRawRational.encode_paid w
  have r := ChargedEdgeDyadicLabels.label_paid n _ (BinaryRawRational.encode_width w)
  simp only [labelCell,BinaryVectorAccess.readMatrix_value,labelCellBudget]
  omega

def labelsControlBudget {R : Type*} [Semiring R] (n b : R) : R :=
  matrixControlBudget n (labelCellBudget n b) (2*BinaryVectorAccess.budget n)

theorem labels_control_paid {n b : ℕ} (D : Input n) (fit : InputFits D b) :
    (labelsWithControl D).2≤labelsControlBudget n b := by
  have width : n.size≤n := BinaryNaturalOperations.size_le_self n
  exact matrix_paid (labelCell D) (labelCell_paid D fit)
    (fun u v => BinaryVectorAccess.readMatrix_paid D.weights u v width width)

@[simp] theorem labels_value {n : ℕ} (D : Input n) : (labels D).1=labelTable D := by
  simp only [labels_reference,batch_value,labelTable,ChargedEdgeDyadicLabels.label_value,BinaryRawRational.encode_value]

def labelsBudget {R : Type*} [Semiring R] (n b : R) : R :=
  n*(n*(40*(b+2)^2+ChargedEdgeDyadicLabels.labelBudget n (b+1)+4)+8*n+4)+8*n+4

theorem labels_paid {n b : ℕ} (D : Input n) (fit : InputFits D b) : (labels D).2 ≤ labelsBudget n b := by
  rw [labels_reference]
  unfold labelsBudget
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

private def keepLabelWithControl {n : ℕ} (l : Labels n) (es : List (Pair n)) : RawNode n → (Bool × ℕ) × ℕ
  | .inl _ => ((true,2),0)
  | .inr x => incidentLoopWithControl l (.inr x) 0 es

private def keepLabel {n : ℕ} (l : Labels n) (es : List (Pair n)) (x : RawNode n) : Bool × ℕ :=
  (keepLabelWithControl l es x).1

private theorem keepLabel_iff {n : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n))
    (correct : es=edges D) (x : RawNode n) : (keepLabel l es x).1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x := by
  subst es
  rcases x with ⟨u,side⟩ | x
  · simp only [keepLabel,keepLabelWithControl,true_iff]
    exact Or.inl ⟨u,side,rfl⟩
  · change (incidentLoop l (.inr x) 0 (edges D)).1=true ↔ _
    simp only [incidentLoop_iff,EdgeToVertex.Active,Sum.inr_ne_inl,exists_false,false_or,edges_mem]

private theorem keepLabel_control_iff {n : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n))
    (correct : es=edges D) (x : RawNode n) :
    (keepLabelWithControl l es x).1.1=true ↔ EdgeToVertex.Active D.graph (labelAt l) x :=
  keepLabel_iff D l es correct x

private theorem keepLabel_paid {n : ℕ} (l : Labels n) (es : List (Pair n)) (x : RawNode n) :
    (keepLabel l es x).2 ≤ es.length*(incidentBudget n+4)+2 := by
  rcases x with x | x
  · simp [keepLabel,keepLabelWithControl]
  · exact (incidentLoop_paid l (.inr x) 0 es).trans (by omega)

private theorem keepLabel_control_paid {n : ℕ} (l : Labels n) (es : List (Pair n)) (x : RawNode n) :
    (keepLabelWithControl l es x).2 ≤
      BinaryShortScan.controlBudget es.length 0 (incidentBudget n+4) (2*BinaryVectorAccess.budget n) := by
  rcases x with x | x
  · exact Nat.zero_le _
  · exact incidentLoop_control_paid l (.inr x) 0 es

private def priceAtWithControl {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) :
    (Code × ℕ) × ℕ :=
  let hit := incidentWithControl l e x
  if hit.1.1 then
    let price := BinaryVectorAccess.readMatrix D.costs e.1 e.2
    ((price.1,hit.1.2+4),hit.2+price.2)
  else ((Code.zero,hit.1.2+4),hit.2)

private def priceAt {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) : Code × ℕ :=
  (priceAtWithControl D l x e).1

private theorem priceAt_reference {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) :
    priceAt D l x e=(if (incident l e x).1 then D.costs[e.1.val][e.2.val] else Code.zero,(incident l e x).2+4) := by
  by_cases hit : (incidentWithControl l e x).1.1=true <;>
    simp only [priceAt,priceAtWithControl,incident,BinaryVectorAccess.readMatrix_value,hit,Bool.false_eq_true,ite_true,ite_false]

private theorem priceAt_control_paid {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) :
    (priceAtWithControl D l x e).2 ≤ 4*BinaryVectorAccess.budget n := by
  have width := BinaryNaturalOperations.size_le_self n
  have incident := incident_control_paid l e x width
  have field := BinaryVectorAccess.readMatrix_paid D.costs e.1 e.2 width width
  unfold priceAtWithControl
  dsimp only
  split <;> dsimp only <;> omega

private theorem priceAt_value {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) :
    (priceAt D l x e).1=edgeCharge D l x e := by
  have distinct : EdgeToVertex.right (labelAt l) e ≠ EdgeToVertex.left (labelAt l) e := by
    simp [EdgeToVertex.right,EdgeToVertex.left]
  by_cases r : x=EdgeToVertex.right (labelAt l) e
  · simp [priceAt_reference,incident_iff,edgeCharge,r,distinct,Code.add,Code.zero]
  · by_cases h : x=EdgeToVertex.left (labelAt l) e
    · simp [priceAt_reference,incident_iff,edgeCharge,h,Ne.symm distinct,Code.add,Code.zero]
    · simp [priceAt_reference,incident_iff,edgeCharge,r,h,Code.add,Code.zero]

private theorem priceAt_fit {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (x : RawNode n) (e : Pair n) : (priceAt D l x e).1.Bounded b := by
  rw [priceAt_reference]
  split
  · exact fit.costs e.1 e.2
  · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)

private def priceFieldsWithControl {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) :
    List (Pair n) → (List Fraction × ℕ) × ℕ
  | [] => (([],1),1)
  | e::es =>
    let c := priceAtWithControl D l x e
    let a := BinaryRawRational.encode c.1.1
    let rest := priceFieldsWithControl D l x es
    let fee := CachedScalarRead.sumMeasured [c.1.2,a.2,rest.1.2,4]
    ((a.1::rest.1.1,fee.1),c.2+fee.2+rest.2+4)

private def priceFields {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (es : List (Pair n)) :
    List Fraction × ℕ := (priceFieldsWithControl D l x es).1

private theorem priceFields_cons {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (e : Pair n) (es : List (Pair n)) :
    priceFields D l x (e::es) =
      let c := priceAt D l x e
      let a := BinaryRawRational.encode c.1
      let rest := priceFields D l x es
      (a.1::rest.1,c.2+a.2+rest.2+4) := by
  simp only [priceFields,priceAt,priceFieldsWithControl,CachedScalarRead.sum_value,List.sum_cons,List.sum_nil,
    Nat.add_zero,Nat.add_assoc]

private theorem priceFields_value {n : ℕ} (D : Input n) (l : Labels n) (x : RawNode n) (es : List (Pair n)) :
    (priceFields D l x es).1 = es.map (fun e => (BinaryRawRational.encode (priceAt D l x e).1).1) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [priceFields_cons,List.map_cons,ih]

private theorem priceFields_paid {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (x : RawNode n) (es : List (Pair n)) :
    (priceFields D l x es).2 ≤ es.length*(40*(b+2)^2+incidentBudget n+8)+1 := by
  induction es with
  | nil => simp only [priceFields,priceFieldsWithControl,List.length_nil,Nat.zero_mul,Nat.zero_add,le_rfl]
  | cons e es ih =>
    have a := BinaryRawRational.encode_paid (priceAt_fit D l fit x e)
    have c := incident_paid l e x
    have oldFee : (priceAt D l x e).2=(incident l e x).2+4 := by rw [priceAt_reference]
    rw [priceFields_cons]
    change (priceAt D l x e).2+
      (BinaryRawRational.encode (priceAt D l x e).1).2+(priceFields D l x es).2+4 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private def priceFieldsStepBudget {R : Type*} [Semiring R] (n e b : R) : R :=
  let fee := e*(40*(b+2)^2+incidentBudget n+8)+1
  4*(96*(fee+2)^2+4)+1+4*BinaryVectorAccess.budget n+4

private theorem priceFields_control_aux {n b e : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (x : RawNode n) (es : List (Pair n)) (small : es.length ≤ e) :
    (priceFieldsWithControl D l x es).2 ≤ es.length*priceFieldsStepBudget n e b+1 := by
  induction es with
  | nil => simp only [priceFieldsWithControl,List.length_nil,Nat.zero_mul,Nat.zero_add,le_rfl]
  | cons arc tail ih =>
    let c := priceAtWithControl D l x arc
    let price := BinaryRawRational.encode c.1.1
    let rest := priceFieldsWithControl D l x tail
    let fees := [c.1.2,price.2,rest.1.2,4]
    let ceiling := e*(40*(b+2)^2+incidentBudget n+8)+1
    have feeValue : fees.sum=(priceFields D l x (arc::tail)).2 := by
      rw [priceFields_cons]
      simp only [fees,c,price,rest,priceAt,priceFields,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
    have reported := (priceFields_paid D l fit x (arc::tail)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ small) 1)
    have width : fees.sum.size≤ceiling := by
      rw [feeValue]
      exact (BinaryNaturalOperations.size_le_self _).trans reported
    have paid := CachedScalarRead.sum_paid fees width
    have priced := priceAt_control_paid D l x arc
    change c.2 ≤ _ at priced
    have child := ih (Nat.le_of_succ_le small)
    change c.2+(CachedScalarRead.sumMeasured fees).2+rest.2+4 ≤ _
    change rest.2 ≤ _ at child
    change (CachedScalarRead.sumMeasured fees).2 ≤ 4*(96*(ceiling+2)^2+4)+1 at paid
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    have overhead : c.2+(CachedScalarRead.sumMeasured fees).2+4≤priceFieldsStepBudget n e b := by
      change _ ≤ 4*(96*(ceiling+2)^2+4)+1+4*BinaryVectorAccess.budget n+4
      omega
    omega

private def priceFieldsControlBudget {R : Type*} [Semiring R] (n e b : R) : R := e*priceFieldsStepBudget n e b+1

private theorem priceFields_control_paid {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (x : RawNode n) (es : List (Pair n)) :
    (priceFieldsWithControl D l x es).2 ≤ priceFieldsControlBudget n es.length b :=
  priceFields_control_aux D l fit x es le_rfl

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

private def nodeCostWithControl {n : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n)) (x : RawNode n) :
    (Code × ℕ) × ℕ :=
  let row := priceFieldsWithControl D l x es
  let rational := BinaryFractionalRows.sum row.1.1
  let decoded := BinaryRawRational.decode rational.1
  let fee := CachedScalarRead.sumMeasured [row.1.2,rational.2,decoded.2,4]
  ((decoded.1,fee.1),row.2+fee.2)

private theorem nodeCost_projection {n : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n)) (x : RawNode n) :
    (nodeCostWithControl D l es x).1=nodeCost D l es x := by
  simp only [nodeCostWithControl,nodeCost,priceFields,CachedScalarRead.sum_value,List.sum_cons,List.sum_nil,
    Nat.add_zero,Nat.add_assoc]

private def nodeCostControlBudget {R : Type*} [Semiring R] (n e b : R) : R :=
  priceFieldsControlBudget n e b+4*(96*(nodeCostBudget n e b+2)^2+4)+1

private theorem nodeCost_control_paid {n b : ℕ} (D : Input n) (l : Labels n) (fit : InputFits D b)
    (es : List (Pair n)) (x : RawNode n) : (nodeCostWithControl D l es x).2 ≤ nodeCostControlBudget n es.length b := by
  let row := priceFieldsWithControl D l x es
  let rational := BinaryFractionalRows.sum row.1.1
  let decoded := BinaryRawRational.decode rational.1
  let fees := [row.1.2,rational.2,decoded.2,4]
  have total : fees.sum=(nodeCost D l es x).2 := by
    simp only [fees,row,rational,decoded,nodeCost,priceFields,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
  have width : fees.sum.size ≤ nodeCostBudget n es.length b := by
    rw [total]
    exact (BinaryNaturalOperations.size_le_self _).trans (nodeCost_paid D l fit es x)
  have paid := CachedScalarRead.sum_paid fees width
  have field := priceFields_control_paid D l fit x es
  change row.2≤_ at field
  change (CachedScalarRead.sumMeasured fees).2 ≤ 4*(96*(nodeCostBudget n es.length b+2)^2+4)+1 at paid
  change row.2+(CachedScalarRead.sumMeasured fees).2≤_
  unfold nodeCostControlBudget
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

private def adjacencyCellWithControl {n : ℕ} (D : Input n) (labels : Labels n) :
    RawNode n → RawNode n → (Bool × ℕ) × ℕ
  | .inr (u,true,i), .inr (v,false,j) =>
    let arc := BinaryVectorAccess.readMatrix D.adjacency u v
    if arc.1 then
      let label := BinaryVectorAccess.readMatrix labels u v
      let a := equalLabel label.1 i
      let b := equalLabel label.1 j
      ((a.1 && b.1,a.2+b.2+8),arc.2+label.2)
    else ((false,4),arc.2)
  | x,y => (adjacencyCell D labels x y,0)

private theorem adjacencyCell_projection {n : ℕ} (D : Input n) (labels : Labels n) (x y : RawNode n) :
    (adjacencyCellWithControl D labels x y).1=adjacencyCell D labels x y := by
  rcases x with ⟨u,b⟩ | ⟨u,b,i⟩ <;> rcases y with ⟨v,c⟩ | ⟨v,c,j⟩ <;>
    cases b <;> cases c <;> try rfl
  simp only [adjacencyCellWithControl,adjacencyCell,BinaryVectorAccess.readMatrix_value,labelAt]
  by_cases live : D.adjacency[u.val][v.val]=true <;> simp [live]

private theorem adjacencyCell_control_paid {n : ℕ} (D : Input n) (labels : Labels n) (x y : RawNode n) :
    (adjacencyCellWithControl D labels x y).2 ≤ 4*BinaryVectorAccess.budget n := by
  rcases x with ⟨u,b⟩ | ⟨u,b,i⟩ <;> rcases y with ⟨v,c⟩ | ⟨v,c,j⟩ <;>
    cases b <;> cases c <;> try exact Nat.zero_le _
  have width := BinaryNaturalOperations.size_le_self n
  have arc := BinaryVectorAccess.readMatrix_paid D.adjacency u v width width
  have label := BinaryVectorAccess.readMatrix_paid labels u v width width
  unfold adjacencyCellWithControl
  dsimp only
  split <;> dsimp only <;> omega

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

private def adjacencyEntry {n m : ℕ} (D : Input n) (l : Labels n) (v : Vector (Node D l) m)
    (i j : Fin m) : (Bool × ℕ) × ℕ :=
  let u := BinaryVectorAccess.read v i
  let w := BinaryVectorAccess.read v j
  let adjacent := adjacencyCellWithControl D l u.1.val w.1.val
  (adjacent.1,u.2+w.2+adjacent.2)

private def adjacencyMatrixWithControl {n m : ℕ} (D : Input n) (l : Labels n) (v : Vector (Node D l) m) :
    (Vector (Vector Bool m) m × ℕ) × ℕ := matrixWithControl (adjacencyEntry D l v)

private theorem adjacencyMatrix_projection {n m : ℕ} (D : Input n) (l : Labels n)
    (v : Vector (Node D l) m) : (adjacencyMatrixWithControl D l v).1=adjacencyMatrix D l v := by
  simp only [adjacencyMatrixWithControl,matrix_reference,adjacencyEntry,BinaryVectorAccess.read_value,
    adjacencyCell_projection,adjacencyMatrix]

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

private def adjacencyControlBudget {R : Type*} [Semiring R] (n m : R) : R :=
  matrixControlBudget m (adjacencyCellBudget n) (2*BinaryVectorAccess.budget m+4*BinaryVectorAccess.budget n)

private theorem adjacencyMatrix_control_paid {n m : ℕ} (D : Input n) (l : Labels n)
    (v : Vector (Node D l) m) : (adjacencyMatrixWithControl D l v).2 ≤ adjacencyControlBudget n m := by
  apply matrix_paid
  · intro i j
    simp only [adjacencyEntry,adjacencyCell_projection]
    exact adjacencyCell_paid D l _ _
  · intro i j
    have width := BinaryNaturalOperations.size_le_self m
    have u := BinaryVectorAccess.read_paid v i width
    have w := BinaryVectorAccess.read_paid v j width
    have side := adjacencyCell_control_paid D l (BinaryVectorAccess.read v i).1.val (BinaryVectorAccess.read v j).1.val
    unfold adjacencyEntry
    dsimp only
    omega

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

private def weightEntry {n m : ℕ} {D : Input n} {l : Labels n} (v : Vector (Node D l) m)
    (i : Fin m) : (Code × ℕ) × ℕ :=
  let node := BinaryVectorAccess.read v i
  (weightField node.1.val,node.2)

private def costEntry {n m : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n))
    (v : Vector (Node D l) m) (i : Fin m) : (Code × ℕ) × ℕ :=
  let node := BinaryVectorAccess.read v i
  let cost := nodeCostWithControl D l es node.1.val
  (cost.1,node.2+cost.2)

private theorem weights_projection {n m : ℕ} {D : Input n} {l : Labels n} (v : Vector (Node D l) m) :
    (BinaryArrayBatch.runWithChildWork (weightEntry v)).1=batch (fun i => weightField v[i.val].val) := by
  rw [BinaryArrayBatch.child_projection]
  change batch _ = batch _
  simp only [weightEntry,BinaryVectorAccess.read_value]

private theorem costs_projection {n m : ℕ} (D : Input n) (l : Labels n) (es : List (Pair n))
    (v : Vector (Node D l) m) :
    (BinaryArrayBatch.runWithChildWork (costEntry D l es v)).1=batch (fun i => nodeCost D l es v[i.val].val) := by
  rw [BinaryArrayBatch.child_projection]
  change batch _ = batch _
  simp only [costEntry,BinaryVectorAccess.read_value,nodeCost_projection]

def buildWithControl {n : ℕ} (D : Input n) : (Prepared D × ℕ) × ℕ :=
  let labeled := labelsWithControl D
  let edges := edgesWithControl D
  let l := labeled.1.1
  let es := edges.1.1
  let nodes := nodeVectorWithControl D l (keepLabelWithControl l es)
    (keepLabel_control_iff D l es (edgesWithCost_value D))
  let v := nodes.1.1
  let adjacency := adjacencyMatrixWithControl D l v
  let weights := BinaryArrayBatch.runWithChildWork (weightEntry v)
  let costs := BinaryArrayBatch.runWithChildWork (costEntry D l es v)
  let g := ⟨v.size,l,v,⟨adjacency.1.1,weights.1.1,costs.1.1⟩⟩
  let fee := CachedScalarRead.sumMeasured [labeled.1.2,weights.1.2,costs.1.2,adjacency.1.2,edges.1.2,nodes.1.2,8]
  ((g,fee.1),labeled.2+edges.2+nodes.2+adjacency.2+weights.2+costs.2+fee.2)

set_option maxHeartbeats 900000 in
theorem build_control_projection {n : ℕ} (D : Input n) : (buildWithControl D).1=build D := by
  let l := (labelsWithControl D).1.1
  let es := (edgesWithControl D).1.1
  let correct := keepLabel_control_iff D l es (edgesWithCost_value D)
  have nodes := nodeVector_reference D l (keepLabelWithControl l es) correct
  simp only [buildWithControl,build,adjacencyMatrix_projection,weights_projection,costs_projection,
    CachedScalarRead.sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
  rw [nodes]
  rfl

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

def controlBudget {R : Type*} [Semiring R] (n b : R) : R :=
  let e := n*n
  let m := dimension n
  let selection := BinaryShortScan.controlBudget e 0 (incidentBudget n+4) (2*BinaryVectorAccess.budget n)
  labelsControlBudget n b+edgesControlBudget n+nodeVectorControlBudget n (e*(incidentBudget n+4)+2) selection+
    adjacencyControlBudget n m+BinaryArrayBatch.childCeiling m (weightBudget n) (BinaryVectorAccess.budget m)+
    BinaryArrayBatch.childCeiling m (nodeCostBudget n e b) (BinaryVectorAccess.budget m+nodeCostControlBudget n e b)+
    7*(96*(budget n b+2)^2+4)+1

set_option maxHeartbeats 1400000 in
theorem build_control_paid {n b : ℕ} (D : Input n) (fit : InputFits D b) :
    (buildWithControl D).2 ≤ controlBudget n b := by
  let labels := labelsWithControl D
  let edges := edgesWithControl D
  let l := labels.1.1
  let es := edges.1.1
  let correct := keepLabel_control_iff D l es (edgesWithCost_value D)
  let nodes := nodeVectorWithControl D l (keepLabelWithControl l es) correct
  let v := nodes.1.1
  let m := (EncodedEdgeGadget.nodes D l).length
  let adjacency := adjacencyMatrixWithControl D l v
  let weights := BinaryArrayBatch.runWithChildWork (weightEntry v)
  let costs := BinaryArrayBatch.runWithChildWork (costEntry D l es v)
  let fees := [labels.1.2,weights.1.2,costs.1.2,adjacency.1.2,edges.1.2,nodes.1.2,8]
  have msize : m ≤ dimension n := by
    have measured : (buildWithControl D).1.1.size=(build D).1.size :=
      congrArg (fun (r : Prepared D × ℕ) => r.1.size) (build_control_projection D)
    change m = (build D).1.size at measured
    exact measured.trans_le (size_le D)
  have esize : es.length≤n*n := by
    have exactEdges : es=EncodedEdgeGadget.edges D := edgesWithCost_value D
    simpa only [exactEdges,pow_two] using edges_length D
  have positive : m.size ≤ m := BinaryNaturalOperations.size_le_self m
  have found := nodeVector_control_paid D l (keepLabelWithControl l es) correct
    (fun x => ⟨keepLabel_paid l es x,keepLabel_control_paid l es x⟩)
  have allNodes : nodes.2 ≤ nodeVectorControlBudget n ((n*n)*(incidentBudget n+4)+2)
      (BinaryShortScan.controlBudget (n*n) 0 (incidentBudget n+4) (2*BinaryVectorAccess.budget n)) := by
    refine found.trans ?_
    unfold nodeVectorControlBudget
    exact BinaryFilter.controlBudget_mono le_rfl (by gcongr)
      (BinaryShortScan.controlBudget_mono esize le_rfl le_rfl le_rfl)
  have adj : adjacency.2 ≤ adjacencyControlBudget n (dimension n) := by
    refine (adjacencyMatrix_control_paid D l v).trans ?_
    unfold adjacencyControlBudget matrixControlBudget BinaryArrayBatch.childCeiling BinaryVectorAccess.budget
    gcongr
  have weight : weights.2 ≤ BinaryArrayBatch.childCeiling (dimension n) (weightBudget n)
      (BinaryVectorAccess.budget (dimension n)) := by
    refine ((BinaryArrayBatch.runWithChildWork_paid (weightEntry v)
      (fun i => weightField_paid (BinaryVectorAccess.read v i).1.val)
      (fun i => BinaryVectorAccess.read_paid v i positive)).trans (BinaryArrayBatch.childBudget_le ..)).trans ?_
    unfold BinaryArrayBatch.childCeiling BinaryVectorAccess.budget
    gcongr
  have cost : costs.2 ≤ BinaryArrayBatch.childCeiling (dimension n) (nodeCostBudget n (n*n) b)
      (BinaryVectorAccess.budget (dimension n)+nodeCostControlBudget n (n*n) b) := by
    have localCost (i : Fin m) : (costEntry D l es v i).2 ≤
        BinaryVectorAccess.budget m+nodeCostControlBudget n es.length b :=
      Nat.add_le_add (BinaryVectorAccess.read_paid v i positive)
        (nodeCost_control_paid D l fit es (BinaryVectorAccess.read v i).1.val)
    have legacyCost (i : Fin m) : (costEntry D l es v i).1.2 ≤ nodeCostBudget n es.length b := by
      simp only [costEntry,nodeCost_projection]
      exact nodeCost_paid D l fit es (BinaryVectorAccess.read v i).1.val
    refine ((BinaryArrayBatch.runWithChildWork_paid (costEntry D l es v) legacyCost localCost).trans
      (BinaryArrayBatch.childBudget_le ..)).trans ?_
    simp only [BinaryArrayBatch.childCeiling,BinaryVectorAccess.budget,nodeCostBudget,nodeCostControlBudget,
      priceFieldsControlBudget,priceFieldsStepBudget]
    gcongr
  have oldFee : fees.sum=(build D).2 := by
    have measured := congrArg (fun (r : Prepared D × ℕ) => r.2) (build_control_projection D)
    change (CachedScalarRead.sumMeasured fees).1=(build D).2 at measured
    rwa [CachedScalarRead.sum_value] at measured
  have width : fees.sum.size≤budget n b := by
    rw [oldFee]
    exact (BinaryNaturalOperations.size_le_self _).trans (build_paid D fit)
  have fee := CachedScalarRead.sum_paid fees width
  have labelsPaid := labels_control_paid D fit
  have edgesPaid := edges_control_paid D
  change (CachedScalarRead.sumMeasured fees).2≤7*(96*(budget n b+2)^2+4)+1 at fee
  change labels.2≤_ at labelsPaid
  change edges.2≤_ at edgesPaid
  unfold controlBudget
  change labels.2+edges.2+nodes.2+adjacency.2+weights.2+costs.2+(CachedScalarRead.sumMeasured fees).2≤_
  dsimp only
  omega

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

attribute [local gcongr] BinaryFilter.controlBudget_mono BinaryShortScan.controlBudget_mono budget_mono

set_option maxHeartbeats 1000000 in
theorem controlBudget_mono {n m a b : ℕ} (size : n ≤ m) (width : a ≤ b) : controlBudget n a ≤ controlBudget m b := by
  simp only [controlBudget,labelsControlBudget,labelCellBudget,edgesControlBudget,nodeVectorControlBudget,
    adjacencyControlBudget,matrixControlBudget,BinaryArrayBatch.childCeiling,BinaryVectorAccess.budget,
    incidentBudget,adjacencyCellBudget,weightBudget,nodeCostBudget,nodeCostControlBudget,
    priceFieldsControlBudget,priceFieldsStepBudget,dimension,ChargedEdgeDyadicLabels.labelBudget,
    ChargedEdgeDyadicLabels.checkBudget]
  gcongr

set_option maxHeartbeats 1000000 in
theorem controlBudget_eval (n b : Polynomial ℕ) (x : ℕ) :
    (controlBudget n b).eval x=controlBudget (n.eval x) (b.eval x) := by
  simp only [controlBudget,labelsControlBudget,labelCellBudget,edgesControlBudget,nodeVectorControlBudget,
    adjacencyControlBudget,matrixControlBudget,BinaryArrayBatch.childCeiling,BinaryVectorAccess.budget,
    incidentBudget,adjacencyCellBudget,weightBudget,nodeCostBudget,nodeCostControlBudget,
    priceFieldsControlBudget,priceFieldsStepBudget,dimension,ChargedEdgeDyadicLabels.labelBudget,
    ChargedEdgeDyadicLabels.checkBudget,budget_eval,BinaryFilter.controlBudget_eval,BinaryShortScan.controlBudget_eval,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_one,Polynomial.eval_zero,
    Polynomial.eval_ofNat]

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
