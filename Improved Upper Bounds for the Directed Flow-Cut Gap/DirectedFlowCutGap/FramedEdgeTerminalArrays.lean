import DirectedFlowCutGap.FramedEdgePackedLayout

/-! The caller converts only a returned line answer. Its cut or witness
array is placed after the schedules of all reached edge rounds. -/
namespace DirectedFlowCutGap.FramedEdgeTerminalArrays

open BinaryArithmetic EncodedArrayStorage Polynomial
open BinaryArrayNestedStorage (Code WithChildren Grid gridSchedule schedule copyBudget cellBudget
  copyBudget_eval cellBudget_eval grid_bounds flat_bounds)
open EncodedEdgeLineInput (lineSize)
open PhysicalAmplifiedVertexSolver (Result)
open PhysicalIntegerRoundingCost (eval_mono)

def code {n : ℕ} (answer : Option (Result (lineSize n))) : Code :=
  match answer with
  | some ⟨.cut _,_,_,_,_⟩ => gridSchedule n n
  | some ⟨.infeasible _,_,_,_,_⟩ => schedule (lineSize n) (fun _ => [])
  | none | some ⟨.invalid,_,_,_,_⟩ => []

def wireCode (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Code :=
  match (PhysicalSourceInputJoin.edge source).1 with
  | none => []
  | some ⟨n,D⟩ =>
    let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
    code (n := n) (PaidDirectEdgeWire.terminalRowLineResult κ raw mode tape)

theorem wire_arrays (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    let placed := wireCode κ mode source tape
    match (PhysicalSourceInputJoin.edge source).1 with
    | none => placed=[]
    | some ⟨n,D⟩ =>
      let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
      match PaidDirectEdgeWire.terminalRowLineResult κ raw mode tape with
      | some ⟨.cut mask,_,_,_,_⟩ => Grid (BinaryEdgeProjection.toEdgesWithControl raw mask).1.1 placed
      | some ⟨.infeasible _,_,_,_,_⟩ =>
        WithChildren (BinaryLineLabels.labelsWithControl n).1.1 (fun _ => []) placed
      | none | some ⟨.invalid,_,_,_,_⟩ => placed=[] := by
  unfold wireCode
  cases (PhysicalSourceInputJoin.edge source).1 with
  | none => rfl
  | some accepted =>
    obtain ⟨n,D⟩ := accepted
    dsimp only
    cases PaidDirectEdgeWire.terminalRowLineResult κ (PhysicalBinaryEdgeWire.decodeWithCost D).1 mode tape with
    | none => rfl
    | some answer =>
      obtain ⟨out,rest,dispatch,readback,charged⟩ := answer
      cases out with
      | cut mask => exact EdgeProjectionArrayStorage.output_cut_arrays _ mask
      | infeasible _ => exact EdgeProjectionArrayStorage.line_label_array n
      | invalid => rfl

private theorem bounds : ∃ cells copies : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (source tape : Bits), fresh (wireCode κ mode source tape) ≤ cells.eval source.length ∧
      (wireCode κ mode source tape).length ≤ copies.eval source.length := by
  let line : Polynomial ℕ := X*2+X*X
  let cells : Polynomial ℕ := (X+1)*cellBudget X+cellBudget line
  let copies : Polynomial ℕ := (X+1)*copyBudget X+copyBudget line
  refine ⟨cells,copies,fun κ mode source tape => ?_⟩
  unfold wireCode
  cases parsed : (PhysicalSourceInputJoin.edge source).1 with
  | none => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | some accepted =>
    obtain ⟨n,D⟩ := accepted
    have original : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ := by
      simpa only [ChargedSourceAssembly.edge_value,← PhysicalSourceInputJoin.edge_value] using parsed
    have size := (ChargedSourceAssembly.edge_dimensions original).1
    have cellAtN : cells.eval n=(n+1)*cellBudget n+cellBudget (lineSize n) := by
      simp only [cells,line,eval_add,eval_mul,eval_X,eval_ofNat,eval_one,cellBudget_eval,lineSize]
    have copyAtN : copies.eval n=(n+1)*copyBudget n+copyBudget (lineSize n) := by
      simp only [copies,line,eval_add,eval_mul,eval_X,eval_ofNat,eval_one,copyBudget_eval,lineSize]
    let ans := PaidDirectEdgeWire.terminalRowLineResult κ (PhysicalBinaryEdgeWire.decodeWithCost D).1 mode tape
    have fixed : fresh (code (n := n) ans) ≤ cells.eval n ∧ (code (n := n) ans).length ≤ copies.eval n := by
      cases ans with
      | none => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
      | some answer =>
        obtain ⟨out,rest,dispatch,readback,charged⟩ := answer
        rw [cellAtN,copyAtN]
        cases out with
        | cut mask =>
          have h := grid_bounds n
          exact ⟨h.2.trans (Nat.le_add_right _ _),h.1.trans (Nat.le_add_right _ _)⟩
        | infeasible _ =>
          have h := flat_bounds (lineSize n)
          exact ⟨h.2.trans (Nat.le_add_left _ _),h.1.trans (Nat.le_add_left _ _)⟩
        | invalid => exact ⟨Nat.zero_le _,Nat.zero_le _⟩
    exact ⟨fixed.1.trans (eval_mono cells size),fixed.2.trans (eval_mono copies size)⟩

set_option maxHeartbeats 1600000 in
theorem polynomialWith (layout : RoundArrayLayout.Runner) (bounded : RoundArrayLayout.Bounded layout) : ∃ cells copies : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let input := PhysicalSourceInputJoin.edgeArrayCode source
      let x := source.length+κ
      ∃ prefixCode rounds : Code,
        (match (PhysicalSourceInputJoin.edge source).1 with
        | none => prefixCode=[]
        | some ⟨_,D⟩ => FramedEdgeStorage.AfterInput D input prefixCode) ∧
        FramedEdgePackedLayout.ModelWith layout κ mode source tape rounds ∧
        let placed := input++prefixCode++rounds++wireCode κ mode source tape
        fresh placed ≤ cells.eval x ∧ placed.length ≤ copies.eval x ∧
        ∀ start : ℕ,
          let extent := allocateTrace start placed
          let width := (start+cells.eval x).size
          let binary := BinaryAllocationTrace.allocate start.bits (placed.map BinaryAllocationTrace.reservation)
          (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=extent ∧
            binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval x) width ∧
            ∀ block∈extent.2, ∀ offset<block.2, (block.1+offset).size ≤ width := by
  obtain ⟨priorCells,priorCopies,prior⟩ := FramedEdgePackedLayout.polynomialWith layout bounded
  obtain ⟨tailCells,tailCopies,after⟩ := bounds
  let cells := priorCells+tailCells
  let copies := priorCopies+tailCopies
  refine ⟨cells,copies,?_⟩
  intro κ mode source tape
  let x := source.length+κ
  obtain ⟨prefixCode,rounds,reached,model,priorSpace,priorWork,_⟩ := prior κ mode source tape
  let before := PhysicalSourceInputJoin.edgeArrayCode source++prefixCode++rounds
  let final := wireCode κ mode source tape
  let placed := before++final
  obtain ⟨tailSpace,tailWork⟩ := after κ mode source tape
  have hs : source.length ≤ x := Nat.le_add_right _ _
  have space : fresh placed ≤ cells.eval x := by
    simpa only [placed,fresh_append,cells,eval_add] using
      Nat.add_le_add (show fresh before ≤ priorCells.eval x from priorSpace) (tailSpace.trans (eval_mono _ hs))
  have work : placed.length ≤ copies.eval x := by
    simpa only [placed,List.length_append,copies,eval_add] using
      Nat.add_le_add (show before.length ≤ priorCopies.eval x from priorWork) (tailWork.trans (eval_mono _ hs))
  refine ⟨prefixCode,rounds,reached,model,space,work,fun start => ?_⟩
  obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout placed start
  have width : (start+fresh placed).size ≤ (start+cells.eval x).size := Nat.size_le_size (Nat.add_le_add_left space start)
  exact ⟨same,paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
    fun block mem offset fits => (widths block mem offset fits).trans width⟩

theorem polynomial : ∃ cells copies : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let input := PhysicalSourceInputJoin.edgeArrayCode source
      let x := source.length+κ
      ∃ prefixCode rounds : Code,
        (match (PhysicalSourceInputJoin.edge source).1 with
        | none => prefixCode=[]
        | some ⟨_,D⟩ => FramedEdgeStorage.AfterInput D input prefixCode) ∧
        FramedEdgePackedLayout.Model κ mode source tape rounds ∧
        let placed := input++prefixCode++rounds++wireCode κ mode source tape
        fresh placed ≤ cells.eval x ∧ placed.length ≤ copies.eval x ∧
        ∀ start : ℕ,
          let extent := allocateTrace start placed
          let width := (start+cells.eval x).size
          let binary := BinaryAllocationTrace.allocate start.bits (placed.map BinaryAllocationTrace.reservation)
          (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=extent ∧
            binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval x) width ∧
            ∀ block∈extent.2, ∀ offset<block.2, (block.1+offset).size ≤ width :=
  polynomialWith RunnerCutoffStorage.Model RunnerCutoffStorage.arrays

end DirectedFlowCutGap.FramedEdgeTerminalArrays
