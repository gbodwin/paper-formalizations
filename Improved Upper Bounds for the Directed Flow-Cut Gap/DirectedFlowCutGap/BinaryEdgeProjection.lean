import DirectedFlowCutGap.BinaryLineLabels
import DirectedFlowCutGap.EncodedEdgeSolver

/-! Charged transport between original edge rows, line masks and dyadic
gadget cuts. Each result agrees with the existing indexed reduction. -/
namespace DirectedFlowCutGap.BinaryEdgeProjection

open BinaryArithmetic EncodedEdgeLineInput RetainedGridState FractionalCoverRawCore
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)
open BinaryEdgeGadget (incident incident_iff incidentBudget incident_paid)

private def coordinateWord {n : ℕ} (ports : Bool) (s t : Fin n) : ℕ × ℕ :=
  let radix := BinaryNaturalView.encode n
  let tail := BinaryNaturalView.encode s.val
  let head := BinaryNaturalView.encode t.val
  let product := mul tail.1 radix.1
  let low := add false head.1 product.1
  let offset := if ports then false::radix.1 else []
  let index := add false offset low.1
  let output := BinaryNaturalView.decode index.1
  (output.1,radix.2+tail.2+head.2+product.2+low.2+index.2+output.2+8)

private theorem coordinateWord_value {n : ℕ} (ports : Bool) (s t : Fin n) :
    (coordinateWord ports s t).1=(if ports then n*2 else 0)+(t.val+n*s.val) := by
  cases ports <;>
    simp only [coordinateWord,BinaryNaturalView.decode_value,(add_spec ..).1,(mul_spec ..).1,
      Bool.false_eq_true,ite_false,ite_true,value,Bool.toNat_false,zero_add,add_zero,BinaryNaturalView.encode_value] <;>
    ring

private theorem coordinateWord_paid {n : ℕ} (ports : Bool) (s t : Fin n) :
    (coordinateWord ports s t).2 ≤ 1024*(n+2)^2 := by
  let radix := BinaryNaturalView.encode n
  let tail := BinaryNaturalView.encode s.val
  let head := BinaryNaturalView.encode t.val
  let product := mul tail.1 radix.1
  let low := add false head.1 product.1
  let offset := if ports then false::radix.1 else []
  let index := add false offset low.1
  have len (x : ℕ) (h : x ≤ n) : (BinaryNaturalView.encode x).1.length ≤ n := by
    rw [BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]
    exact (BinaryNaturalOperations.size_le_self x).trans h
  have encodePaid (x : ℕ) (h : x ≤ n) : (BinaryNaturalView.encode x).2 ≤ 16*(n+1)^2 :=
    (BinaryNaturalView.encode_paid x).trans (Nat.mul_le_mul_left 16
      (Nat.pow_le_pow_left (Nat.add_le_add_right ((BinaryNaturalOperations.size_le_self x).trans h) 1) 2))
  have lR : radix.1.length ≤ n := len n le_rfl
  have lT : tail.1.length ≤ n := len s.val s.isLt.le
  have lH : head.1.length ≤ n := len t.val t.isLt.le
  have p := mul_spec tail.1 radix.1
  have pLen : product.1.length ≤ 3*n+1 := p.2.1.trans (by omega)
  have pPaid : product.2 ≤ 128*(n+1)^2 := by
    apply p.2.2.trans
    calc
      _ ≤ 64*(n+1)*(2*n+2) := by gcongr; omega
      _ = _ := by ring
  have l := add_spec false head.1 product.1
  have lLen : low.1.length ≤ 3*n+2 := l.2.1.trans (by omega)
  have lPaid : low.2 ≤ 16*(3*n+2) := l.2.2.trans (by omega)
  have preLen : offset.length ≤ n+1 := by
    cases ports <;> simp [offset,lR]
  have i := add_spec false offset low.1
  have iLen : index.1.length ≤ 3*n+3 := i.2.1.trans (by omega)
  have iPaid : index.2 ≤ 16*(3*n+3) := i.2.2.trans (by omega)
  have decoded := (BinaryNaturalView.decode_paid index.1).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (show index.1.length+1 ≤ 3*n+4 by omega) 2))
  change radix.2+tail.2+head.2+product.2+low.2+index.2+(BinaryNaturalView.decode index.1).2+8 ≤ _
  have rPaid : radix.2 ≤ 16*(n+1)^2 := encodePaid n le_rfl
  have tPaid : tail.2 ≤ 16*(n+1)^2 := encodePaid s.val s.isLt.le
  have hPaid : head.2 ≤ 16*(n+1)^2 := encodePaid t.val t.isLt.le
  nlinarith only [rPaid,tPaid,hPaid,pPaid,lPaid,iPaid,decoded]

private def arcPosition {n : ℕ} (s t : Fin n) : Fin (lineSize n) × ℕ :=
  let result := coordinateWord true s t
  (⟨result.1,by
    rw [coordinateWord_value]
    exact (edgeIndex (s,t)).isLt⟩,result.2)

@[simp] private theorem arcPosition_value {n : ℕ} (s t : Fin n) :
    (arcPosition s t).1=edgeIndex (s,t) := Fin.ext (coordinateWord_value true s t)

private def gridWithControl {n k : ℕ} {A : Type}
    (position : Fin n → Fin n → Fin k × ℕ)
    (f : Fin n → Fin n → Fin k → (A × ℕ) × ℕ) : (Vector (Vector A n) n × ℕ) × ℕ :=
  BinaryArrayBatch.runWithChildWork fun s => BinaryArrayBatch.runWithChildWork fun t =>
    let atCell := position s t
    let result := f s t atCell.1
    ((result.1.1,atCell.2+result.1.2),result.2)

private theorem grid_reference {n k : ℕ} {A : Type}
    (position : Fin n → Fin n → Fin k × ℕ)
    (f : Fin n → Fin n → Fin k → (A × ℕ) × ℕ) :
    (gridWithControl position f).1 = batch (fun s => batch fun t =>
      let atCell := position s t
      let result := (f s t atCell.1).1
      (result.1,atCell.2+result.2)) := by
  unfold gridWithControl
  rw [BinaryArrayBatch.child_projection]
  change batch _ = batch _
  congr 1
  funext s
  rw [BinaryArrayBatch.child_projection]
  rfl

def readbackBudget {R : Type*} [Semiring R] (n cell : R) : R :=
  n*(n*(1024*(n+2)^2+cell)+8*n+4)+8*n+4

private theorem grid_legacy_paid {n k : ℕ} {A : Type}
    (position : Fin n → Fin n → Fin k × ℕ)
    (f : Fin n → Fin n → Fin k → (A × ℕ) × ℕ) {cap : ℕ}
    (indexPaid : ∀ s t, (position s t).2 ≤ 1024*(n+2)^2)
    (paid : ∀ s t i, (f s t i).1.2 ≤ cap) : (gridWithControl position f).1.2 ≤ readbackBudget n cap := by
  rw [grid_reference]
  unfold readbackBudget
  apply batch_paid
  intro s
  apply batch_paid
  intro t
  exact Nat.add_le_add (indexPaid s t) (paid s t _)

def gridControlBudget {R : Type*} [Semiring R] (n fee work : R) : R :=
  let cellFee := 1024*(n+2)^2+fee
  BinaryArrayBatch.childCeiling n (n*cellFee+8*n+4)
    (BinaryArrayBatch.childCeiling n cellFee work)

private theorem grid_control_paid {n k : ℕ} {A : Type}
    (position : Fin n → Fin n → Fin k × ℕ)
    (f : Fin n → Fin n → Fin k → (A × ℕ) × ℕ) {cap work : ℕ}
    (indexPaid : ∀ s t, (position s t).2 ≤ 1024*(n+2)^2)
    (paid : ∀ s t i, (f s t i).1.2 ≤ cap) (measured : ∀ s t i, (f s t i).2 ≤ work) :
    (gridWithControl position f).2 ≤ gridControlBudget n cap work := by
  let cellFee := 1024*(n+2)^2+cap
  let cell (s t : Fin n) : (A × ℕ) × ℕ :=
    let atCell := position s t
    let result := f s t atCell.1
    ((result.1.1,atCell.2+result.1.2),result.2)
  have legacy (s t : Fin n) : (cell s t).1.2 ≤ cellFee :=
    Nat.add_le_add (indexPaid s t) (paid s t _)
  have rowFee (s : Fin n) :
      (BinaryArrayBatch.runWithChildWork (cell s)).1.2 ≤ n*cellFee+8*n+4 := by
    rw [BinaryArrayBatch.child_projection]
    exact batch_paid _ (legacy s)
  have rowWork (s : Fin n) :
      (BinaryArrayBatch.runWithChildWork (cell s)).2 ≤ BinaryArrayBatch.childCeiling n cellFee work :=
    (BinaryArrayBatch.runWithChildWork_paid _ (legacy s) (fun t => measured s t _)).trans
      (BinaryArrayBatch.childBudget_le ..)
  exact (BinaryArrayBatch.runWithChildWork_paid _ rowFee rowWork).trans (BinaryArrayBatch.childBudget_le ..)

private def matrixPosition {n : ℕ} (s t : Fin n) : Fin (n*n) × ℕ :=
  let result := coordinateWord false s t
  (⟨result.1,by
    have inside := (finProdFinEquiv (s,t)).isLt
    change t.val+n*s.val<n*n at inside
    simpa only [result,coordinateWord_value,Bool.false_eq_true,ite_false,zero_add] using inside⟩,result.2)

@[simp] private theorem matrixPosition_value {n : ℕ} (s t : Fin n) :
    (matrixPosition s t).1=finProdFinEquiv (s,t) := by
  apply Fin.ext
  change (coordinateWord false s t).1=t.val+n*s.val
  simpa only [Bool.false_eq_true,ite_false,zero_add] using coordinateWord_value false s t

def matrixWithControl {n : ℕ} {A : Type} (f : Fin (n*n) → (A × ℕ) × ℕ) :
    (Vector (Vector A n) n × ℕ) × ℕ := gridWithControl matrixPosition (fun _ _ => f)

def matrix {n : ℕ} {A : Type} (f : Fin (n*n) → A × ℕ) : Vector (Vector A n) n × ℕ :=
  (matrixWithControl fun i => (f i,0)).1

theorem matrix_reference {n : ℕ} {A : Type} (f : Fin (n*n) → (A × ℕ) × ℕ) :
    (matrixWithControl f).1 = matrix (fun i => (f i).1) := by
  simp only [matrix,matrixWithControl,grid_reference]

@[simp] theorem matrix_value {n : ℕ} {A : Type} (f : Fin (n*n) → A × ℕ) :
    (matrix f).1=Vector.ofFn (fun s => Vector.ofFn fun t => (f (finProdFinEquiv (s,t))).1) := by
  simp only [matrix,matrixWithControl,grid_reference,batch_value,matrixPosition_value]

theorem matrix_paid {n : ℕ} {A : Type} (f : Fin (n*n) → A × ℕ) {cap : ℕ}
    (paid : ∀ i, (f i).2 ≤ cap) : (matrix f).2 ≤ readbackBudget n cap :=
  grid_legacy_paid matrixPosition (fun _ _ i => (f i,0)) (coordinateWord_paid false) (fun _ _ => paid)

theorem matrix_control_paid {n : ℕ} {A : Type} (f : Fin (n*n) → (A × ℕ) × ℕ) {cap work : ℕ}
    (paid : ∀ i, (f i).1.2 ≤ cap) (measured : ∀ i, (f i).2 ≤ work) :
    (matrixWithControl f).2 ≤ gridControlBudget n cap work :=
  grid_control_paid matrixPosition (fun _ _ => f) (coordinateWord_paid false) (fun _ _ => paid) (fun _ _ => measured)

private theorem lineWidth (n : ℕ) : n.size ≤ lineSize n :=
  (BinaryNaturalOperations.size_le_self n).trans (by unfold lineSize; omega)

def roundingInputWithControl {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    (EncodedEdgeGadget.Input n × ℕ) × ℕ :=
  let weights := gridWithControl arcPosition fun _ _ i =>
    let cell := BinaryVectorAccess.read row i
    ((cell.1,4),cell.2)
  ((⟨D.adjacency,weights.1.1,D.costs⟩,weights.1.2+4),weights.2)

def roundingInput {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) : EncodedEdgeGadget.Input n × ℕ :=
  (roundingInputWithControl D row).1

theorem roundingInput_reference {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    roundingInput D row =
      let weights := batch fun s => batch fun t =>
        let position := arcPosition s t
        (get row position.1,position.2+4)
      (⟨D.adjacency,weights.1,D.costs⟩,weights.2+4) := by
  simp only [roundingInput,roundingInputWithControl,grid_reference,BinaryVectorAccess.read_value,FractionalCoverRawCore.get]

@[simp] theorem roundingInput_value {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    (roundingInput D row).1=EncodedEdgeLineInput.roundingInput D row := by
  simp only [roundingInput_reference,batch_value,arcPosition_value,EncodedEdgeLineInput.roundingInput]

def roundingBudget {R : Type*} [Semiring R] (n : R) : R := readbackBudget n 4+4

theorem roundingInput_paid {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    (roundingInput D row).2 ≤ roundingBudget n := by
  unfold roundingInput roundingInputWithControl roundingBudget
  apply Nat.add_le_add_right
  exact grid_legacy_paid arcPosition _ (coordinateWord_paid true) (fun _ _ _ => le_rfl)

theorem roundingInput_control_paid {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    (roundingInputWithControl D row).2 ≤ gridControlBudget n 4 (BinaryVectorAccess.budget (lineSize n)) := by
  unfold roundingInputWithControl
  dsimp only
  exact grid_control_paid arcPosition
    (fun _ _ i => let stored := BinaryVectorAccess.read row i; ((stored.1,4),stored.2))
    (coordinateWord_paid true) (fun _ _ _ => le_rfl)
    (fun _ _ i => BinaryVectorAccess.read_paid row i (BinaryNaturalOperations.size_le_self _))

private def edgeCell {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) (s t : Fin n) (i : Fin (lineSize n)) :
    (Bool × ℕ) × ℕ :=
  let live := BinaryVectorAccess.readMatrix D.adjacency s t
  if live.1 then
    let selected := BinaryVectorAccess.read mask i
    ((selected.1,8),live.2+selected.2)
  else ((false,8),live.2)

private theorem edgeCell_reference {n : ℕ} (D : Input n) (mask : Flags (lineSize n))
    (s t : Fin n) (i : Fin (lineSize n)) : (edgeCell D mask s t i).1=(D.adjacency[s.val][t.val] && mask[i.val],8) := by
  simp only [edgeCell,BinaryVectorAccess.readMatrix_value]
  cases D.adjacency[s.val][t.val] <;> simp [BinaryVectorAccess.read_value]

def toEdgesWithControl {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) : (PairFlags n × ℕ) × ℕ :=
  gridWithControl arcPosition (edgeCell D mask)

def toEdges {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) : PairFlags n × ℕ :=
  (toEdgesWithControl D mask).1

theorem toEdges_reference {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) : toEdges D mask =
    batch (fun s => batch fun t =>
      let atCell := arcPosition s t
      (D.adjacency[s.val][t.val] && mask[atCell.1.val],atCell.2+8)) := by
  simp only [toEdges,toEdgesWithControl,grid_reference,edgeCell_reference]

@[simp] theorem toEdges_value {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) :
    (toEdges D mask).1=EncodedEdgeLineInput.toEdges D mask := by
  simp only [toEdges_reference,batch_value,arcPosition_value,EncodedEdgeLineInput.toEdges]

theorem toEdges_paid {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) :
    (toEdges D mask).2 ≤ readbackBudget n 8 := by
  apply grid_legacy_paid arcPosition _ (coordinateWord_paid true)
  simp only [edgeCell_reference,le_refl,implies_true]

theorem toEdges_control_paid {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) :
    (toEdgesWithControl D mask).2 ≤ gridControlBudget n 8 (3*BinaryVectorAccess.budget (lineSize n)) := by
  apply grid_control_paid arcPosition _ (coordinateWord_paid true)
  · simp only [edgeCell_reference,le_refl,implies_true]
  · intro s t i
    have adjacency := BinaryVectorAccess.readMatrix_paid D.adjacency s t (lineWidth n) (lineWidth n)
    have selected := BinaryVectorAccess.read_paid mask i (BinaryNaturalOperations.size_le_self _)
    unfold edgeCell
    dsimp only
    split <;> dsimp only <;> omega

private def lineCell {n : ℕ} (labels : Vector (EdgeLineReduction.Node (Fin n)) (lineSize n))
    (mask : PairFlags n) (i : Fin (lineSize n)) : (Bool × ℕ) × ℕ :=
  let label := BinaryVectorAccess.read labels i
  match label.1 with
  | .inl _ => ((false,2),label.2)
  | .inr (s,t) =>
      let selected := BinaryVectorAccess.readMatrix mask s t
      ((selected.1,4),label.2+selected.2)

private theorem lineCell_reference {n : ℕ} (labels : Vector (EdgeLineReduction.Node (Fin n)) (lineSize n))
    (mask : PairFlags n) (i : Fin (lineSize n)) : (lineCell labels mask i).1 =
    match labels[i.val] with
    | .inl _ => (false,2)
    | .inr (s,t) => (mask[s.val][t.val],4) := by
  simp only [lineCell,BinaryVectorAccess.read_value]
  rcases labels[i.val] with port | ⟨s,t⟩ <;> simp only [BinaryVectorAccess.readMatrix_value]

def toLineWithControl {n : ℕ} (mask : PairFlags n) : (Flags (lineSize n) × ℕ) × ℕ :=
  let labels := BinaryLineLabels.labelsWithControl n
  let copies := BinaryArrayBatch.runWithChildWork (lineCell labels.1.1 mask)
  ((copies.1.1,labels.1.2+copies.1.2+2),labels.2+copies.2)

def toLine {n : ℕ} (mask : PairFlags n) : Flags (lineSize n) × ℕ :=
  (toLineWithControl mask).1

theorem toLine_reference {n : ℕ} (mask : PairFlags n) : toLine mask =
    let labels := BinaryLineLabels.labels n
    let copies := batch fun i : Fin (lineSize n) => match labels.1[i.val] with
      | .inl _ => (false,2)
      | .inr (s,t) => (mask[s.val][t.val],4)
    (copies.1,labels.2+copies.2+2) := by
  have plain := BinaryArrayBatch.child_projection (lineCell (BinaryLineLabels.labels n).1 mask)
  change (BinaryArrayBatch.runWithChildWork (lineCell (BinaryLineLabels.labels n).1 mask)).1 = batch _ at plain
  change ((let labels := BinaryLineLabels.labels n
    let copies := (BinaryArrayBatch.runWithChildWork (lineCell labels.1 mask)).1
    (copies.1,labels.2+copies.2+2))) = _
  dsimp only
  rw [plain]
  simp only [lineCell_reference]

@[simp] theorem toLine_value {n : ℕ} (mask : PairFlags n) :
    (toLine mask).1=EncodedEdgeLineInput.toLine mask := by
  simp only [toLine_reference,batch_value,BinaryLineLabels.labels_value,Vector.getElem_ofFn,EncodedEdgeLineInput.toLine]
  congr
  funext i
  cases index n i with
  | inl port => rfl
  | inr arc => cases arc; rfl

def lineMaskBudget {R : Type*} [Semiring R] (n : R) : R :=
  let m := n*2+n*n
  BinaryLineLabels.budget n m+m*4+8*m+6

theorem lineMaskBudget_mono {n m : ℕ} (h : n ≤ m) : lineMaskBudget n ≤ lineMaskBudget m := by
  unfold lineMaskBudget BinaryLineLabels.budget
  dsimp only
  gcongr

theorem toLine_paid {n : ℕ} (mask : PairFlags n) : (toLine mask).2 ≤ lineMaskBudget n := by
  let labels := BinaryLineLabels.labels n
  let step (i : Fin (lineSize n)) : Bool × ℕ := match labels.1[i.val] with
    | .inl _ => (false,2)
    | .inr (s,t) => (mask[s.val][t.val],4)
  have paid := batch_paid step (cap := 4) (fun i => by
    unfold step
    rcases labels.1[i.val] with port | ⟨s,t⟩ <;> simp)
  have labelPaid := BinaryLineLabels.labels_paid n
  change labels.2 ≤ _ at labelPaid
  unfold lineMaskBudget
  rw [toLine_reference]
  change labels.2+(batch step).2+2 ≤ BinaryLineLabels.budget n (lineSize n)+lineSize n*4+8*lineSize n+6
  omega

def lineMaskControlBudget {R : Type*} [Semiring R] (m : R) : R :=
  BinaryLineLabels.labelControlBudget m+BinaryArrayBatch.childCeiling m 4 (3*BinaryVectorAccess.budget m)

theorem toLine_control_paid {n : ℕ} (mask : PairFlags n) :
    (toLineWithControl mask).2 ≤ lineMaskControlBudget (lineSize n) := by
  let m := lineSize n
  let labels := BinaryLineLabels.labelsWithControl n
  have legacy (i : Fin m) : (lineCell labels.1.1 mask i).1.2 ≤ 4 := by
    rw [lineCell_reference]
    rcases labels.1.1[i.val] with port | ⟨s,t⟩ <;> simp
  have measured (i : Fin m) : (lineCell labels.1.1 mask i).2 ≤ 3*BinaryVectorAccess.budget m := by
    have label := BinaryVectorAccess.read_paid labels.1.1 i (BinaryNaturalOperations.size_le_self m)
    unfold lineCell
    dsimp only
    split
    · omega
    · rename_i s t _
      have cell := BinaryVectorAccess.readMatrix_paid mask s t (lineWidth n) (lineWidth n)
      change _ ≤ 2*BinaryVectorAccess.budget m at cell
      omega
  have copied := (BinaryArrayBatch.runWithChildWork_paid _ legacy measured).trans (BinaryArrayBatch.childBudget_le ..)
  exact Nat.add_le_add (BinaryLineLabels.labels_control_paid n) copied

private def incidentAt {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (i : Fin g.size) : (Bool × ℕ) × ℕ :=
  let selected := BinaryVectorAccess.read mask i
  if selected.1 then
    let node := BinaryVectorAccess.read g.vertices i
    let hit := BinaryEdgeGadget.incidentWithControl g.labels edge node.1.val
    ((hit.1.1,hit.1.2+4),selected.2+node.2+hit.2)
  else ((false,4),selected.2)

private theorem incidentAt_reference {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (i : Fin g.size) :
    (incidentAt g mask edge i).1 = if mask[i.val] then
      let hit := incident g.labels edge g.vertices[i.val].val
      (hit.1,hit.2+4)
    else (false,4) := by
  simp only [incidentAt,BinaryVectorAccess.read_value]
  split <;> rfl

private theorem incidentAt_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (i : Fin g.size) :
    (incidentAt g mask edge i).1.2 ≤ incidentBudget n+4 ∧
      (incidentAt g mask edge i).2 ≤ 2*BinaryVectorAccess.budget g.size+2*BinaryVectorAccess.budget n := by
  constructor
  · rw [incidentAt_reference]
    split
    · exact Nat.add_le_add_right (incident_paid g.labels edge g.vertices[i.val].val) 4
    · exact Nat.le_add_left _ _
  · have width := BinaryNaturalOperations.size_le_self g.size
    have selected := BinaryVectorAccess.read_paid mask i width
    have vertex := BinaryVectorAccess.read_paid g.vertices i width
    have hit := BinaryEdgeGadget.incident_control_paid g.labels edge (BinaryVectorAccess.read g.vertices i).1.val
      (BinaryNaturalOperations.size_le_self n)
    unfold incidentAt
    dsimp only
    split <;> dsimp only <;> omega

private def hasIncidentWithControl {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (paid : ℕ) (is : List (Fin g.size)) : (Bool × ℕ) × ℕ :=
  BinaryShortScan.run (incidentAt g mask edge) paid is

private def hasIncident {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (paid : ℕ) (is : List (Fin g.size)) : Bool × ℕ :=
  (hasIncidentWithControl g mask edge paid is).1

private theorem hasIncident_reference {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (paid : ℕ) (is : List (Fin g.size)) :
    hasIncident g mask edge paid is = BinaryShortScan.reference (fun i => if mask[i.val] then
      let hit := incident g.labels edge g.vertices[i.val].val
      (hit.1,hit.2+4)
    else (false,4)) paid is := by
  simp only [hasIncident,hasIncidentWithControl,BinaryShortScan.run_reference,incidentAt_reference]

private theorem hasIncident_iff {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (paid : ℕ) (is : List (Fin g.size)) :
    (hasIncident g mask edge paid is).1=true ↔
      ∃ i ∈ is, mask[i.val]=true ∧
        (g.vertices[i.val].val=EdgeToVertex.right (EncodedEdgeGadget.labelAt g.labels) edge ∨
         g.vertices[i.val].val=EdgeToVertex.left (EncodedEdgeGadget.labelAt g.labels) edge) := by
  simp only [hasIncident_reference,BinaryShortScan.reference_true]
  refine exists_congr (fun i => and_congr_right (fun _ => ?_))
  cases mask[i.val] <;> simp [incident_iff]

private theorem hasIncident_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (paid : ℕ) (is : List (Fin g.size)) :
    (hasIncident g mask edge paid is).2 ≤ paid+is.length*(incidentBudget n+4)+1 := by
  simp only [hasIncident,hasIncidentWithControl,BinaryShortScan.run_reference]
  exact BinaryShortScan.reference_paid _ _ _ _ (fun i _ => (incidentAt_paid g mask edge i).1)

private def scanIndices (m : ℕ) : List (Fin m) × ℕ :=
  let indices := BinaryArrayBatch.run fun i : Fin m => (i,0)
  (indices.1.1.toList,indices.2+4*m+2)

private theorem scanIndices_value (m : ℕ) : (scanIndices m).1=List.finRange m := by
  simp only [scanIndices,BinaryArrayBatch.run_value,Vector.toList_ofFn,List.finRange]

private def cellWithControl {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (is : List (Fin g.size)) (s t : Fin n) : (Bool × ℕ) × ℕ :=
  let arc := BinaryVectorAccess.readMatrix D.adjacency s t
  if arc.1 then
    let test := hasIncidentWithControl g mask (s,t) 0 is
    ((test.1.1,test.1.2+4),arc.2+test.2)
  else ((false,4),arc.2)

private theorem cell_reference {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (is : List (Fin g.size)) (s t : Fin n) : (cellWithControl g mask is s t).1 =
    if D.adjacency[s.val][t.val] then
      let test := hasIncident g mask (s,t) 0 is
      (test.1,test.2+4)
    else (false,4) := by
  simp only [cellWithControl,BinaryVectorAccess.readMatrix_value]
  split <;> rfl

private def edgeMaskWithControl {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (PairFlags n × ℕ) × ℕ :=
  let indices := scanIndices g.size
  let bits := gridWithControl (fun _ _ : Fin n => ((0 : Fin 1),0))
    (fun s t _ => cellWithControl g mask indices.1 s t)
  ((bits.1.1,bits.1.2+8*g.size+4),indices.2+bits.2)

private def edgeMask {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : PairFlags n × ℕ := (edgeMaskWithControl g mask).1

private theorem edgeMask_reference {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : edgeMask g mask =
    let indices := List.finRange g.size
    let bits := batch fun s : Fin n => batch fun t : Fin n =>
      if D.adjacency[s.val][t.val] then
        let test := hasIncident g mask (s,t) 0 indices
        (test.1,test.2+4)
      else (false,4)
    (bits.1,bits.2+8*g.size+4) := by
  simp only [edgeMask,edgeMaskWithControl,grid_reference,scanIndices_value,cell_reference,Nat.zero_add,Prod.eta]

set_option maxHeartbeats 900000 in
private theorem edgeMask_value {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (edgeMask g mask).1=EncodedEdgeRounding.pullback g mask := by
  apply Vector.ext
  intro s hs
  apply Vector.ext
  intro t ht
  apply Bool.eq_iff_iff.mpr
  simp only [edgeMask_reference,batch_value,Vector.getElem_ofFn,EncodedEdgeRounding.pullback]
  split
  · rename_i live
    simp only [live,Bool.true_and,Bool.or_eq_true]
    change (hasIncident g mask (⟨s,hs⟩,⟨t,ht⟩) 0 (List.finRange g.size)).1=true ↔
      ((List.finRange g.size).any fun i => mask[i.val] &&
          decide (g.vertices[i.val].val=EdgeToVertex.right (EncodedEdgeGadget.labelAt g.labels) (⟨s,hs⟩,⟨t,ht⟩)))=true ∨
      ((List.finRange g.size).any fun i => mask[i.val] &&
          decide (g.vertices[i.val].val=EdgeToVertex.left (EncodedEdgeGadget.labelAt g.labels) (⟨s,hs⟩,⟨t,ht⟩)))=true
    simp only [hasIncident_iff,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true,decide_eq_true_eq,
      and_or_left,exists_or]
  · simp_all

def maskBudget {R : Type*} [Semiring R] (n m : R) : R :=
  n*(n*(m*(incidentBudget n+4)+5)+8*n+4)+8*n+4+8*m+4

private theorem edgeMask_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (edgeMask g mask).2 ≤ maskBudget n g.size := by
  rw [edgeMask_reference]
  unfold maskBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply batch_paid
  intro s
  apply batch_paid
  intro t
  have paid := hasIncident_paid g mask (s,t) 0 (List.finRange g.size)
  rw [List.length_finRange,zero_add] at paid
  split <;> dsimp only <;> omega

private def scanControlBudget {R : Type*} [Semiring R] (n m : R) : R :=
  BinaryShortScan.controlBudget m 0 (incidentBudget n+4)
    (2*BinaryVectorAccess.budget m+2*BinaryVectorAccess.budget n)

private def maskControlBudget {R : Type*} [Semiring R] (n m : R) : R :=
  BinaryArrayBatch.childCeiling m 0 0+4*m+2+
    gridControlBudget n (m*(incidentBudget n+4)+5) (2*BinaryVectorAccess.budget n+scanControlBudget n m)

private theorem edgeMask_control_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (edgeMaskWithControl g mask).2 ≤ maskControlBudget n g.size := by
  let indices := scanIndices g.size
  have len : indices.1.length=g.size := by rw [show indices.1=List.finRange g.size from scanIndices_value _]; simp
  have gather := (BinaryArrayBatch.run_paid (fun i : Fin g.size => (i,0)) (fun _ => le_rfl)).trans
    (BinaryArrayBatch.childBudget_le g.size 0 0)
  have legacy (s t : Fin n) : (cellWithControl g mask indices.1 s t).1.2 ≤ g.size*(incidentBudget n+4)+5 := by
    rw [cell_reference]
    have scan := hasIncident_paid g mask (s,t) 0 indices.1
    rw [len,zero_add] at scan
    split <;> dsimp only <;> omega
  have measured (s t : Fin n) : (cellWithControl g mask indices.1 s t).2 ≤
      2*BinaryVectorAccess.budget n+scanControlBudget n g.size := by
    have width := BinaryNaturalOperations.size_le_self n
    have arc := BinaryVectorAccess.readMatrix_paid D.adjacency s t width width
    have scan := BinaryShortScan.run_paid (incidentAt g mask (s,t)) 0 (incidentBudget n+4)
      (2*BinaryVectorAccess.budget g.size+2*BinaryVectorAccess.budget n) indices.1
      (fun i _ => incidentAt_paid g mask (s,t) i)
    rw [len] at scan
    change (hasIncidentWithControl g mask (s,t) 0 indices.1).2 ≤ scanControlBudget n g.size at scan
    unfold cellWithControl
    dsimp only
    split <;> dsimp only <;> omega
  have bits := grid_control_paid (fun _ _ : Fin n => ((0 : Fin 1),0))
    (fun s t _ => cellWithControl g mask indices.1 s t) (fun _ _ => Nat.zero_le _)
    (fun s t _ => legacy s t) (fun s t _ => measured s t)
  unfold edgeMaskWithControl maskControlBudget scanIndices
  dsimp only
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_right gather _) _) bits

def pullbackWithControl {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (Flags (lineSize n) × ℕ) × ℕ :=
  let original := edgeMaskWithControl g mask
  let line := toLineWithControl original.1.1
  ((line.1.1,original.1.2+line.1.2),original.2+line.2)

def pullback {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : Flags (lineSize n) × ℕ := (pullbackWithControl g mask).1

theorem pullback_reference {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : pullback g mask =
      let original := edgeMask g mask
      let line := toLine original.1
      (line.1,original.2+line.2) := rfl

def pullbackControlBudget {R : Type*} [Semiring R] (n m : R) : R :=
  maskControlBudget n m+lineMaskControlBudget (n*2+n*n)

theorem pullback_control_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (pullbackWithControl g mask).2 ≤ pullbackControlBudget n g.size :=
  Nat.add_le_add (edgeMask_control_paid g mask) (toLine_control_paid _)

@[simp] theorem pullback_value {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) :
    (pullback g mask).1=EncodedEdgeLineInput.toLine (EncodedEdgeRounding.pullback g mask) := by
  simp only [pullback_reference,toLine_value,edgeMask_value]

def pullbackBudget {R : Type*} [Semiring R] (n m : R) : R := maskBudget n m+lineMaskBudget n

theorem pullback_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (pullback g mask).2 ≤ pullbackBudget n g.size :=
  Nat.add_le_add (edgeMask_paid g mask) (toLine_paid _)

private def readPorts {n : ℕ} (labels : Vector (EdgeLineReduction.Node (Fin n)) (lineSize n))
    (demand : Fin (lineSize n) × Fin (lineSize n)) : Option (Fin n × Fin n) × ℕ :=
  let fromLabel := BinaryVectorAccess.read labels demand.1
  let toLabel := BinaryVectorAccess.read labels demand.2
  let original := match fromLabel.1,toLabel.1 with
    | .inl (s,true), .inl (t,false) => some (s,t)
    | _,_ => none
  (original,fromLabel.2+toLabel.2)

def outputWithControl {n : ℕ} (D : Input n) :
    EncodedVertexSolver.Output (lineSize n) → (EncodedEdgeSolver.Output n × ℕ) × ℕ
  | .infeasible demand =>
    let labels := BinaryLineLabels.labelsWithControl n
    let original := readPorts labels.1.1 demand
    ((.infeasible original.1,labels.1.2+8),labels.2+original.2)
  | .cut a =>
    let kept := toEdgesWithControl D a
    ((.cut kept.1.1,kept.1.2+2),kept.2)
  | .invalid => ((.invalid,2),0)

def output {n : ℕ} (D : Input n) (r : EncodedVertexSolver.Output (lineSize n)) :
    EncodedEdgeSolver.Output n × ℕ := (outputWithControl D r).1

theorem output_reference {n : ℕ} (D : Input n) (r : EncodedVertexSolver.Output (lineSize n)) : output D r =
    match r with
    | .infeasible demand =>
      let labels := BinaryLineLabels.labels n
      let original := match labels.1[demand.1.val],labels.1[demand.2.val] with
        | .inl (s,true), .inl (t,false) => some (s,t)
        | _,_ => none
      (.infeasible original,labels.2+8)
    | .cut a => let kept := toEdges D a; (.cut kept.1,kept.2+2)
    | .invalid => (.invalid,2) := by
  cases r <;> simp only [output,outputWithControl,readPorts,BinaryVectorAccess.read_value] <;> rfl

@[simp] theorem output_value {n : ℕ} (D : Input n) (r : EncodedVertexSolver.Output (lineSize n)) :
    (output D r).1=EncodedEdgeSolver.outputFor D r := by
  cases r with
  | infeasible d =>
    simp only [output_reference,BinaryLineLabels.labels_value,Vector.getElem_ofFn]
    rfl
  | cut a =>
    simp only [output_reference,toEdges_value,EncodedEdgeSolver.outputFor]
  | invalid => rfl

def outputBudget {R : Type*} [Semiring R] (n : R) : R :=
  readbackBudget n 8+BinaryLineLabels.budget n (n*2+n*n)+8

theorem output_paid {n : ℕ} (D : Input n) (r : EncodedVertexSolver.Output (lineSize n)) :
    (output D r).2 ≤ outputBudget n := by
  rw [output_reference]
  cases r with
  | infeasible d =>
    have paid := BinaryLineLabels.labels_paid n
    change (BinaryLineLabels.labels n).2+8 ≤ readbackBudget n 8+BinaryLineLabels.budget n (lineSize n)+8
    omega
  | cut a =>
    have paid := toEdges_paid D a
    change (toEdges D a).2+2 ≤ readbackBudget n 8+BinaryLineLabels.budget n (lineSize n)+8
    omega
  | invalid =>
    change 2 ≤ readbackBudget n 8+BinaryLineLabels.budget n (n*2+n*n)+8
    omega

def outputControlBudget {R : Type*} [Semiring R] (n : R) : R :=
  let m := n*2+n*n
  gridControlBudget n 8 (3*BinaryVectorAccess.budget m)+BinaryLineLabels.labelControlBudget m+
    2*BinaryVectorAccess.budget m

theorem output_control_paid {n : ℕ} (D : Input n) (r : EncodedVertexSolver.Output (lineSize n)) :
    (outputWithControl D r).2 ≤ outputControlBudget n := by
  let m := lineSize n
  let labels := BinaryLineLabels.labelsWithControl n
  cases r with
  | infeasible d =>
    have a := BinaryLineLabels.labels_control_paid n
    have b := BinaryVectorAccess.read_paid labels.1.1 d.1 (BinaryNaturalOperations.size_le_self m)
    have c := BinaryVectorAccess.read_paid labels.1.1 d.2 (BinaryNaturalOperations.size_le_self m)
    change labels.2+((BinaryVectorAccess.read labels.1.1 d.1).2+(BinaryVectorAccess.read labels.1.1 d.2).2) ≤ _
    change labels.2 ≤ BinaryLineLabels.labelControlBudget m at a
    unfold outputControlBudget
    change _ ≤ gridControlBudget n 8 (3*BinaryVectorAccess.budget m)+BinaryLineLabels.labelControlBudget m+
      2*BinaryVectorAccess.budget m
    omega
  | cut a =>
    apply (toEdges_control_paid D a).trans
    change gridControlBudget n 8 (3*BinaryVectorAccess.budget m) ≤
      gridControlBudget n 8 (3*BinaryVectorAccess.budget m)+BinaryLineLabels.labelControlBudget m+
        2*BinaryVectorAccess.budget m
    omega
  | invalid => exact Nat.zero_le _

open Polynomial in
theorem gridControlBudget_eval (n fee work : Polynomial ℕ) (x : ℕ) :
    (gridControlBudget n fee work).eval x=gridControlBudget (n.eval x) (fee.eval x) (work.eval x) := by
  simp only [gridControlBudget,BinaryArrayBatch.childCeiling,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

open Polynomial in
theorem outputControlBudget_eval (n : Polynomial ℕ) (x : ℕ) :
    (outputControlBudget n).eval x=outputControlBudget (n.eval x) := by
  simp only [outputControlBudget,gridControlBudget_eval,BinaryLineLabels.labelControlBudget,
    BinaryArrayBatch.childCeiling,BinaryVectorAccess.budget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_zero]

theorem pullbackControlBudget_mono {n n' m m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    pullbackControlBudget n m ≤ pullbackControlBudget n' m' := by
  unfold pullbackControlBudget maskControlBudget gridControlBudget lineMaskControlBudget
    BinaryLineLabels.labelControlBudget BinaryArrayBatch.childCeiling BinaryVectorAccess.budget incidentBudget
  dsimp only
  gcongr
  apply BinaryShortScan.controlBudget_mono hm le_rfl
  · unfold incidentBudget
    gcongr
  · unfold BinaryVectorAccess.budget
    gcongr

open Polynomial in
theorem pullbackControlBudget_eval (n m : Polynomial ℕ) (x : ℕ) :
    (pullbackControlBudget n m).eval x=pullbackControlBudget (n.eval x) (m.eval x) := by
  simp only [pullbackControlBudget,maskControlBudget,gridControlBudget_eval,scanControlBudget,
    BinaryShortScan.controlBudget_eval,lineMaskControlBudget,BinaryLineLabels.labelControlBudget,
    BinaryArrayBatch.childCeiling,BinaryVectorAccess.budget,incidentBudget,eval_add,eval_mul,eval_pow,
    eval_ofNat,eval_one,eval_zero]

open Polynomial in
theorem lineMaskBudget_eval (p : Polynomial ℕ) (x : ℕ) :
    (lineMaskBudget p).eval x=lineMaskBudget (p.eval x) := by
  simp only [lineMaskBudget,BinaryLineLabels.budget_eval,eval_add,eval_mul,eval_ofNat]

open Polynomial in
theorem pullbackBudget_eval (p q : Polynomial ℕ) (x : ℕ) :
    (pullbackBudget p q).eval x=pullbackBudget (p.eval x) (q.eval x) := by
  simp only [pullbackBudget,maskBudget,incidentBudget,lineMaskBudget_eval,eval_add,eval_mul,eval_pow,eval_ofNat]

def originalMask {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : PairFlags n × ℕ :=
  let projected := edgeMaskWithControl g mask
  (projected.1.1,projected.1.2+projected.2)

theorem originalMask_value {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (originalMask g mask).1 = EncodedEdgeRounding.pullback g mask :=
  edgeMask_value g mask

theorem originalMask_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (originalMask g mask).2 ≤ pullbackBudget n g.size+pullbackControlBudget n g.size :=
  Nat.add_le_add ((edgeMask_paid g mask).trans (Nat.le_add_right ..))
    ((edgeMask_control_paid g mask).trans (Nat.le_add_right ..))

end DirectedFlowCutGap.BinaryEdgeProjection
