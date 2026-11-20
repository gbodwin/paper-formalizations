import DirectedFlowCutGap.FramedEdgeStorage
import DirectedFlowCutGap.EdgeRoundStorage
import DirectedFlowCutGap.LiteralRoundSchedule

/-! Join the modeled array work of all attempted rounds to the original
edge input. Rejected inputs and skipped rounds contribute no round arrays. -/
namespace DirectedFlowCutGap.FramedEdgeRoundLayout

open BinaryArithmetic EncodedArrayStorage Polynomial
open BinaryArrayNestedStorage (Code)
open ChargedPhysicalVertexSolver (rowsCount)
open EncodedEdgeLineInput (lineSize)
open PhysicalIntegerRoundingCost (eval_mono)

private theorem rows_le_terminal {n : ℕ} (cover : PhysicalCoverReader.Plan n) :
    rowsCount cover ≤ (BinaryCoverReadback.terminalArrayCode cover).length := by
  cases cover with
  | invalid | infeasible _ | zero _ => exact Nat.zero_le _
  | covers rows =>
    induction rows with
    | nil => exact Nat.zero_le _
    | cons head tail ih =>
      change tail.length ≤ (BinaryCoverReadback.terminalArrayCode (.covers tail)).length at ih
      change (head::tail).length ≤
        ((TerminalArrayAssembly.schedule head.toList).map PackedArraySchedule.shape ++
          BinaryCoverReadback.terminalArrayCode (.covers tail)).length
      have headLength := (TerminalArrayAssembly.space head.toList).1
      simp only [List.length_cons,List.length_append,List.length_map,headLength]
      omega

private theorem visit_bounds {A : Type} (visits : List A) (code : A → Code) (cells copies : ℕ)
    (fits : ∀ x ∈ visits, fresh (code x) ≤ cells ∧ (code x).length ≤ copies) :
    fresh (visits.flatMap code) ≤ visits.length*cells ∧ (visits.flatMap code).length ≤ visits.length*copies := by
  induction visits with
  | nil => simp [fresh]
  | cons head tail ih =>
    have here := fits head List.mem_cons_self
    have after := ih (fun x hx => fits x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons,fresh_append,List.length_cons,List.length_append,Nat.add_mul,Nat.one_mul]
    omega

def rounds {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : EncodedEdgeInput.Input n)
    (tape : Bits) : Code :=
  let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
  let line := (PhysicalAmplifiedBinaryEdge.lineWithCost raw).1
  let measured := PhysicalSourceReadback.runWithTerminalCharge line
  match measured.1 with
  | none => []
  | some (cover,_,_) =>
    let controls := BinarySolverOuterControls.edge n κ
    let ready := BinaryAmplificationPreparation.prepare line.costs controls.draws controls.extra controls.confidence
    let visited := LiteralRoundSchedule.amplified line (PaidDirectEdgeWire.roundWithGadgetWork raw mode)
      controls.draws controls.extra controls.confidence cover tape
    visited.1.flatMap fun visit => EdgeRoundStorage.roundCode raw mode ready.trials visit.input.weights visit.tape

def sourceRounds (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) : Code :=
  match (PhysicalSourceInputJoin.edge source).1 with
  | none => []
  | some ⟨_,D⟩ => rounds κ mode D tape

set_option maxHeartbeats 2100000 in
theorem polynomial : ∃ cells copies : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
    let pre := PhysicalSourceInputJoin.edgeArrayCode source
    ∃ post : Code,
      (match (PhysicalSourceInputJoin.edge source).1 with
      | none => post=[]
      | some ⟨_,D⟩ => FramedEdgeStorage.AfterInput D pre post) ∧
      let code := pre++post++sourceRounds κ mode source tape
      let x := source.length+κ
      fresh code ≤ cells.eval x ∧ code.length ≤ copies.eval x ∧
      ∀ start : ℕ,
        let placed := allocateTrace start code
        let width := (start+cells.eval x).size
        let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
          binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval x) width ∧
          ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width := by
  obtain ⟨preCells,preCopies,prefixBounds⟩ := FramedEdgeStorage.array_polynomial
  obtain ⟨roundCells,roundCopies,roundBounds⟩ := EdgeRoundStorage.polynomial
  let count := ((X+2)*X+1)*preCopies
  let cells := preCells+count*roundCells
  let copies := preCopies+count*roundCopies
  refine ⟨cells,copies,?_⟩
  intro κ mode source tape
  let pre := PhysicalSourceInputJoin.edgeArrayCode source
  let x := source.length+κ
  obtain ⟨post,reached,hs,hw,_⟩ := prefixBounds source
  let initial := pre++post
  let added := sourceRounds κ mode source tape
  let total := initial++added
  have room : source.length ≤ x := Nat.le_add_right _ _
  have further : fresh added ≤ (count*roundCells).eval x ∧ added.length ≤ (count*roundCopies).eval x := by
    unfold added sourceRounds
    cases parsed : (PhysicalSourceInputJoin.edge source).1 with
    | none => exact ⟨by simp [fresh],Nat.zero_le _⟩
    | some data =>
      obtain ⟨n,D⟩ := data
      let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
      let line := (PhysicalAmplifiedBinaryEdge.lineWithCost raw).1
      let cover := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput line).1
      let controls := BinarySolverOuterControls.edge n κ
      let ready := BinaryAmplificationPreparation.prepare line.costs controls.draws controls.extra controls.confidence
      let visited := LiteralRoundSchedule.amplified line (PaidDirectEdgeWire.roundWithGadgetWork raw mode)
        controls.draws controls.extra controls.confidence cover tape
      let one (visit : LiteralRoundSchedule.Visit (lineSize n)) :=
        EdgeRoundStorage.roundCode raw mode ready.trials visit.input.weights visit.tape
      obtain ⟨dispatch,_,reader,_,read,_⟩ := PhysicalSourceReadback.terminal_headers line
      have relative : FramedEdgeStorage.AfterInput D pre post := by
        simpa only [parsed] using reached
      obtain ⟨priceCode,lineCode,cache,_,_,tail,_,_⟩ := relative
      have terminalCode : post=priceCode++lineCode++(cache++BinaryCoverReadback.terminalArrayCode cover) := tail
      have terminal : rowsCount cover ≤ preCopies.eval x := by
        apply (rows_le_terminal cover).trans
        apply le_trans _ (hw.trans (eval_mono preCopies room))
        rw [terminalCode]
        simp only [List.length_append]
        omega
      have stored : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ :=
        (ChargedSourceAssembly.edge_value source).trans ((PhysicalSourceInputJoin.edge_value source).symm.trans parsed)
      have dim : n ≤ x := (ChargedSourceAssembly.edge_dimensions stored).1.trans room
      have extra : controls.extra+1 ≤ ((X+2)*X+1 : Polynomial ℕ).eval x := by
        simp only [controls,BinarySolverOuterControls.edge_extra,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
        have confidence : κ ≤ x := Nat.le_add_left _ _
        exact Nat.add_le_add_right ((PhysicalSolverCostEnvelope.exponent_le n κ).trans
          (Nat.mul_le_mul (Nat.add_le_add_right dim 2) confidence)) 1
      have visits : visited.1.length ≤ count.eval x := by
        apply (LiteralRoundSchedule.amplified_count ..).trans
        rw [eval_mul]
        exact Nat.mul_le_mul extra terminal
      have modeled := visit_bounds visited.1 one (roundCells.eval x) (roundCopies.eval x) (fun v _ => by
        have bound := roundBounds raw mode ready.trials v.input.weights v.tape
        exact ⟨bound.1.trans (eval_mono roundCells dim),bound.2.trans (eval_mono roundCopies dim)⟩)
      have measured : rounds κ mode D tape=visited.1.flatMap one := by
        have readyPlan : (PhysicalSourceReadback.runWithTerminalCharge
            (PhysicalAmplifiedBinaryEdge.lineWithCost (PhysicalBinaryEdgeWire.decodeWithCost D).1).1).1=
            some (cover,dispatch,reader) := read
        simp only [rounds,readyPlan]
        rfl
      change fresh (rounds κ mode D tape) ≤ (count*roundCells).eval x ∧
        (rounds κ mode D tape).length ≤ (count*roundCopies).eval x
      simp only [measured,eval_mul]
      exact ⟨modeled.1.trans (Nat.mul_le_mul_right _ visits),modeled.2.trans (Nat.mul_le_mul_right _ visits)⟩
  have cellCount : fresh total ≤ cells.eval x := by
    simp only [total,fresh_append,cells,eval_add]
    exact Nat.add_le_add (hs.trans (eval_mono preCells room)) further.1
  have copyCount : total.length ≤ copies.eval x := by
    simp only [total,List.length_append,copies,eval_add]
    exact Nat.add_le_add (hw.trans (eval_mono preCopies room)) further.2
  refine ⟨post,reached,cellCount,copyCount,fun start => ?_⟩
  obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout total start
  have fits : (start+fresh total).size ≤ (start+cells.eval x).size :=
    Nat.size_le_size (Nat.add_le_add_left cellCount start)
  exact ⟨same,paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
    fun block member offset inside => (widths block member offset inside).trans fits⟩

end DirectedFlowCutGap.FramedEdgeRoundLayout
