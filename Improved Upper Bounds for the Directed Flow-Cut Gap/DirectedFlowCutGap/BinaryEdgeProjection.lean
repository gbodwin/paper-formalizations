import DirectedFlowCutGap.BinaryLineLabels
import DirectedFlowCutGap.EncodedEdgeSolver

/-! Charged transport between original edge rows, line masks and dyadic
gadget cuts. Each result agrees with the existing indexed reduction. -/
namespace DirectedFlowCutGap.BinaryEdgeProjection

open BinaryArithmetic EncodedEdgeLineInput RetainedGridState FractionalCoverRawCore
open BinaryVertexReductionArithmetic (batch batch_value batch_paid)
open BinaryEdgeGadget (incident incident_iff incidentBudget incident_paid)

private def arcWord {n : ℕ} (s t : Fin n) : ℕ × ℕ :=
  let radix := BinaryNaturalView.encode n
  let tail := BinaryNaturalView.encode s.val
  let head := BinaryNaturalView.encode t.val
  let product := mul tail.1 radix.1
  let low := add false head.1 product.1
  let index := add false (false::radix.1) low.1
  let output := BinaryNaturalView.decode index.1
  (output.1,radix.2+tail.2+head.2+product.2+low.2+index.2+output.2+8)

private theorem arcWord_value {n : ℕ} (s t : Fin n) : (arcWord s t).1=(edgeIndex (s,t)).val := by
  change _ = n*2+(t.val+n*s.val)
  simp only [arcWord,BinaryNaturalView.decode_value,(add_spec ..).1,(mul_spec ..).1,
    value,Bool.toNat_false,zero_add,add_zero,BinaryNaturalView.encode_value]
  ring

private theorem arcWord_paid {n : ℕ} (s t : Fin n) :
    (arcWord s t).2 ≤ 1024*(n+2)^2 := by
  let radix := BinaryNaturalView.encode n
  let tail := BinaryNaturalView.encode s.val
  let head := BinaryNaturalView.encode t.val
  let product := mul tail.1 radix.1
  let low := add false head.1 product.1
  let index := add false (false::radix.1) low.1
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
  have i := add_spec false (false::radix.1) low.1
  rw [List.length_cons] at i
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
  let result := arcWord s t
  (⟨result.1,by rw [arcWord_value]; exact (edgeIndex (s,t)).isLt⟩,result.2)

@[simp] private theorem arcPosition_value {n : ℕ} (s t : Fin n) :
    (arcPosition s t).1=edgeIndex (s,t) := Fin.ext (arcWord_value s t)

private def batchArcs {n : ℕ} {A : Type} (f : Fin n → Fin n → Fin (lineSize n) → A × ℕ) :
    Vector (Vector A n) n × ℕ :=
  batch fun s => batch fun t =>
    let position := arcPosition s t
    let answer := f s t position.1
    (answer.1,position.2+answer.2)

def readbackBudget {R : Type*} [Semiring R] (n cell : R) : R :=
  n*(n*(1024*(n+2)^2+cell)+8*n+4)+8*n+4

private theorem batchArcs_paid {n : ℕ} {A : Type}
    (f : Fin n → Fin n → Fin (lineSize n) → A × ℕ) {cap : ℕ}
    (paid : ∀ s t i, (f s t i).2 ≤ cap) : (batchArcs f).2 ≤ readbackBudget n cap := by
  unfold batchArcs readbackBudget
  apply batch_paid
  intro s
  apply batch_paid
  intro t
  exact Nat.add_le_add (arcWord_paid s t) (paid s t _)

def roundingInput {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) : EncodedEdgeGadget.Input n × ℕ :=
  let weight := batchArcs fun _ _ i => (get row i,4)
  (⟨D.adjacency,weight.1,D.costs⟩,weight.2+4)

@[simp] theorem roundingInput_value {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    (roundingInput D row).1=EncodedEdgeLineInput.roundingInput D row := by
  simp only [roundingInput,batchArcs,batch_value,arcPosition_value,EncodedEdgeLineInput.roundingInput]

def roundingBudget {R : Type*} [Semiring R] (n : R) : R := readbackBudget n 4+4

theorem roundingInput_paid {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    (roundingInput D row).2 ≤ roundingBudget n := by
  unfold roundingInput roundingBudget
  apply Nat.add_le_add_right
  exact batchArcs_paid (fun _ _ i => (get row i,4)) (fun _ _ _ => le_rfl)

def toEdges {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) : PairFlags n × ℕ :=
  batchArcs fun s t i => (D.adjacency[s.val][t.val] && mask[i.val],8)

@[simp] theorem toEdges_value {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) :
    (toEdges D mask).1=EncodedEdgeLineInput.toEdges D mask := by
  simp only [toEdges,batchArcs,batch_value,arcPosition_value,EncodedEdgeLineInput.toEdges]

theorem toEdges_paid {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) :
    (toEdges D mask).2 ≤ readbackBudget n 8 := batchArcs_paid _ (fun _ _ _ => le_rfl)

def toLine {n : ℕ} (mask : PairFlags n) : Flags (lineSize n) × ℕ :=
  let labels := BinaryLineLabels.labels n
  let copies := batch fun i : Fin (lineSize n) => match labels.1[i.val] with
    | .inl _ => (false,2)
    | .inr (s,t) => (mask[s.val][t.val],4)
  (copies.1,labels.2+copies.2+2)

@[simp] theorem toLine_value {n : ℕ} (mask : PairFlags n) :
    (toLine mask).1=EncodedEdgeLineInput.toLine mask := by
  simp only [toLine,batch_value,BinaryLineLabels.labels_value,Vector.getElem_ofFn,EncodedEdgeLineInput.toLine]
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
  change labels.2+(batch step).2+2 ≤ BinaryLineLabels.budget n (lineSize n)+lineSize n*4+8*lineSize n+6
  omega

private def hasIncident {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (paid : ℕ) :
    List (Fin g.size) → Bool × ℕ
  | [] => (false,paid+1)
  | i::is =>
    if mask[i.val] then
      let test := incident g.labels edge g.vertices[i.val].val
      if test.1 then (true,paid+test.2+4)
      else hasIncident g mask edge (paid+test.2+4) is
    else hasIncident g mask edge (paid+4) is

private theorem hasIncident_iff {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (paid : ℕ) (is : List (Fin g.size)) :
    (hasIncident g mask edge paid is).1=true ↔
      ∃ i ∈ is, mask[i.val]=true ∧
        (g.vertices[i.val].val=EdgeToVertex.right (EncodedEdgeGadget.labelAt g.labels) edge ∨
         g.vertices[i.val].val=EdgeToVertex.left (EncodedEdgeGadget.labelAt g.labels) edge) := by
  induction is generalizing paid with
  | nil => simp [hasIncident]
  | cons i is ih =>
    simp only [hasIncident,List.mem_cons,exists_eq_or_imp]
    split
    · split <;> simp_all [incident_iff]
    · simp_all

private theorem hasIncident_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) (edge : EncodedEdgeGadget.Pair n) (paid : ℕ) (is : List (Fin g.size)) :
    (hasIncident g mask edge paid is).2 ≤ paid+is.length*(incidentBudget n+4)+1 := by
  induction is generalizing paid with
  | nil => simp [hasIncident]
  | cons i is ih =>
    have test := incident_paid g.labels edge g.vertices[i.val].val
    simp only [hasIncident,List.length_cons,Nat.add_mul,Nat.one_mul]
    split
    · split
      · dsimp only
        omega
      · exact (ih _).trans (by omega)
    · exact (ih _).trans (by omega)

private def edgeMask {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : PairFlags n × ℕ :=
  let indices := List.finRange g.size
  let bits := batch fun s : Fin n => batch fun t : Fin n =>
    if D.adjacency[s.val][t.val] then
      let test := hasIncident g mask (s,t) 0 indices
      (test.1,test.2+4)
    else (false,4)
  (bits.1,bits.2+8*g.size+4)

private theorem edgeMask_value {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (edgeMask g mask).1=EncodedEdgeRounding.pullback g mask := by
  apply Vector.ext
  intro s hs
  apply Vector.ext
  intro t ht
  apply Bool.eq_iff_iff.mpr
  simp only [edgeMask,batch_value,Vector.getElem_ofFn,EncodedEdgeRounding.pullback]
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
  unfold edgeMask maskBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply batch_paid
  intro s
  apply batch_paid
  intro t
  have paid := hasIncident_paid g mask (s,t) 0 (List.finRange g.size)
  rw [List.length_finRange,zero_add] at paid
  split <;> dsimp only <;> omega

def pullback {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : Flags (lineSize n) × ℕ :=
  let original := edgeMask g mask
  let line := toLine original.1
  (line.1,original.2+line.2)

@[simp] theorem pullback_value {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) :
    (pullback g mask).1=EncodedEdgeLineInput.toLine (EncodedEdgeRounding.pullback g mask) := by
  simp only [pullback,toLine_value,edgeMask_value]

def pullbackBudget {R : Type*} [Semiring R] (n m : R) : R := maskBudget n m+lineMaskBudget n

theorem pullback_paid {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : (pullback g mask).2 ≤ pullbackBudget n g.size :=
  Nat.add_le_add (edgeMask_paid g mask) (toLine_paid _)

def output {n : ℕ} (D : Input n) :
    EncodedVertexSolver.Output (lineSize n) → EncodedEdgeSolver.Output n × ℕ
  | .infeasible demand =>
    let labels := BinaryLineLabels.labels n
    let original := match labels.1[demand.1.val], labels.1[demand.2.val] with
      | .inl (s,true), .inl (t,false) => some (s,t)
      | _,_ => none
    (.infeasible original,labels.2+8)
  | .cut a =>
    let kept := toEdges D a
    (.cut kept.1,kept.2+2)
  | .invalid => (.invalid,2)

@[simp] theorem output_value {n : ℕ} (D : Input n) (r : EncodedVertexSolver.Output (lineSize n)) :
    (output D r).1=EncodedEdgeSolver.outputFor D r := by
  cases r with
  | infeasible d =>
    simp only [output,BinaryLineLabels.labels_value,Vector.getElem_ofFn]
    rfl
  | cut a =>
    simp only [output,toEdges_value,EncodedEdgeSolver.outputFor]
  | invalid => rfl

def outputBudget {R : Type*} [Semiring R] (n : R) : R :=
  readbackBudget n 8+BinaryLineLabels.budget n (n*2+n*n)+8

theorem output_paid {n : ℕ} (D : Input n) (r : EncodedVertexSolver.Output (lineSize n)) :
    (output D r).2 ≤ outputBudget n := by
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

open Polynomial in
theorem lineMaskBudget_eval (p : Polynomial ℕ) (x : ℕ) :
    (lineMaskBudget p).eval x=lineMaskBudget (p.eval x) := by
  simp only [lineMaskBudget,BinaryLineLabels.budget_eval,eval_add,eval_mul,eval_ofNat]

open Polynomial in
theorem pullbackBudget_eval (p q : Polynomial ℕ) (x : ℕ) :
    (pullbackBudget p q).eval x=pullbackBudget (p.eval x) (q.eval x) := by
  simp only [pullbackBudget,maskBudget,incidentBudget,lineMaskBudget_eval,eval_add,eval_mul,eval_pow,eval_ofNat]

end DirectedFlowCutGap.BinaryEdgeProjection
