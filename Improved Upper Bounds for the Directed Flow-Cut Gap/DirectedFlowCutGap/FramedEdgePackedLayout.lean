import DirectedFlowCutGap.FramedEdgeRoundLayout
import DirectedFlowCutGap.FramedEdgeTrials
import DirectedFlowCutGap.EdgePackedRoundLayout

/-! Place the cutoff model at the corresponding visit of the original edge
solver. The visit list stops after a failed round. -/
namespace DirectedFlowCutGap.FramedEdgePackedLayout

open BinaryArithmetic EncodedArrayStorage Polynomial
open BinaryArrayNestedStorage (Code gridSchedule)
open EncodedEdgeLineInput (lineSize)
open PhysicalIntegerRoundingCost (eval_mono)

def Model (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) (code : Code) : Prop :=
  match (PhysicalSourceInputJoin.edge source).1 with
  | none => code=[]
  | some ⟨n,D⟩ =>
    let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
    let line := (PhysicalAmplifiedBinaryEdge.lineWithCost raw).1
    match (PhysicalSourceReadback.runWithTerminalCharge line).1 with
    | none => code=[]
    | some (cover,_,_) =>
      let controls := BinarySolverOuterControls.edge n κ
      let ready := BinaryAmplificationPreparation.prepare line.costs controls.draws controls.extra controls.confidence
      let visited := LiteralRoundSchedule.amplified line (PaidDirectEdgeWire.roundWithGadgetWork raw mode)
        controls.draws controls.extra controls.confidence cover tape
      ∃ parts : List Code, code=parts.flatten ∧ List.Forall₂
        (fun visit part => EdgePackedRoundLayout.Model raw mode ready.trials visit.input.weights visit.tape part)
        visited.1 parts

private theorem collect {A : Type} (r : A → Code → Prop) (visits : List A) (cells copies : ℕ)
    (each : ∀ v ∈ visits, ∃ code, r v code ∧ fresh code ≤ cells ∧ code.length ≤ copies) :
    ∃ parts : List Code, List.Forall₂ r visits parts ∧ fresh parts.flatten ≤ visits.length*cells ∧
      parts.flatten.length ≤ visits.length*copies := by
  induction visits with
  | nil => exact ⟨[],.nil,Nat.zero_le _,Nat.zero_le _⟩
  | cons head tail ih =>
    obtain ⟨front,headRun,headSpace,headWork⟩ := each head List.mem_cons_self
    obtain ⟨rest,tailRun,tailSpace,tailWork⟩ := ih (fun v present => each v (List.mem_cons_of_mem _ present))
    refine ⟨front::rest,.cons headRun tailRun,?_,?_⟩ <;>
      simp only [List.flatten_cons,List.length_cons,List.length_append,fresh_append,Nat.add_mul,Nat.one_mul] <;>
      omega

private theorem visit_count {n : ℕ} (raw : EncodedEdgeLineInput.Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (visits : List (LiteralRoundSchedule.Visit (lineSize n))) :
    visits.length ≤ (visits.flatMap fun v => EdgeRoundStorage.roundCode raw mode T v.input.weights v.tape).length := by
  have grid : 1 ≤ (gridSchedule n n).length := by
    simp only [gridSchedule,BinaryArrayNestedStorage.schedule,List.length_append,List.length_cons,List.length_nil]
    omega
  induction visits with
  | nil => rfl
  | cons head tail ih =>
    have first : 1 ≤ (EdgeRoundStorage.roundCode raw mode T head.input.weights head.tape).length := by
      unfold EdgeRoundStorage.roundCode
      simp only [List.length_append]
      omega
    simp only [List.flatMap_cons,List.length_cons,List.length_append]
    omega

set_option maxHeartbeats 2200000 in
theorem polynomial : ∃ cells copies : Polynomial ℕ,
    ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
    let pre := PhysicalSourceInputJoin.edgeArrayCode source
    let x := source.length+κ
    ∃ prefixCode roundCode : Code,
      (match (PhysicalSourceInputJoin.edge source).1 with
      | none => prefixCode=[]
      | some ⟨_,D⟩ => FramedEdgeStorage.AfterInput D pre prefixCode) ∧ Model κ mode source tape roundCode ∧
      let code := pre++prefixCode++roundCode
      fresh code ≤ cells.eval x ∧ code.length ≤ copies.eval x ∧
      ∀ start : ℕ,
        let placed := allocateTrace start code
        let width := (start+cells.eval x).size
        let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
          binary.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval x) width ∧
          ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size ≤ width := by
  obtain ⟨beforeCells,beforeCopies,before⟩ := FramedEdgeRoundLayout.polynomial
  obtain ⟨trials,trialBound⟩ := FramedEdgeTrials.polynomial
  obtain ⟨roundCells,roundCopies,roundBound⟩ := EdgePackedRoundLayout.arrays
  let pad := X+trials
  let afterCells := beforeCopies*roundCells.comp pad
  let afterCopies := beforeCopies*roundCopies.comp pad
  let cells := beforeCells+afterCells
  let copies := beforeCopies+afterCopies
  refine ⟨cells,copies,?_⟩
  intro κ mode source tape
  let x := source.length+κ
  let pre := PhysicalSourceInputJoin.edgeArrayCode source
  obtain ⟨prefixCode,reached,priorSpace,priorWork,_⟩ := before κ mode source tape
  let first := pre++prefixCode
  let earlier := FramedEdgeRoundLayout.sourceRounds κ mode source tape
  have previousSpace : fresh first+fresh earlier ≤ beforeCells.eval x := by
    rw [← fresh_append]
    exact priorSpace
  have previousWork : first.length+earlier.length ≤ beforeCopies.eval x := by
    rw [← List.length_append]
    exact priorWork
  have space : fresh first ≤ beforeCells.eval x :=
    (Nat.le_add_right (fresh first) (fresh earlier)).trans previousSpace
  have work : first.length ≤ beforeCopies.eval x :=
    (Nat.le_add_right first.length earlier.length).trans previousWork
  have count : earlier.length ≤ beforeCopies.eval x :=
    (Nat.le_add_left earlier.length first.length).trans previousWork
  have extra : ∃ code, Model κ mode source tape code ∧
      fresh code ≤ afterCells.eval x ∧ code.length ≤ afterCopies.eval x := by
    unfold Model
    cases parsed : (PhysicalSourceInputJoin.edge source).1 with
    | none => exact ⟨[],rfl,Nat.zero_le _,Nat.zero_le _⟩
    | some saved =>
      obtain ⟨n,D⟩ := saved
      let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
      let line := (PhysicalAmplifiedBinaryEdge.lineWithCost raw).1
      let cover := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput line).1
      let controls := BinarySolverOuterControls.edge n κ
      let ready := BinaryAmplificationPreparation.prepare line.costs controls.draws controls.extra controls.confidence
      let visited := LiteralRoundSchedule.amplified line (PaidDirectEdgeWire.roundWithGadgetWork raw mode)
        controls.draws controls.extra controls.confidence cover tape
      obtain ⟨dispatch,_,reader,_,read,_⟩ := PhysicalSourceReadback.terminal_headers line
      have readyPlan : (PhysicalSourceReadback.runWithTerminalCharge
          (PhysicalAmplifiedBinaryEdge.lineWithCost (PhysicalBinaryEdgeWire.decodeWithCost D).1).1).1=
          some (cover,dispatch,reader) := read
      have exactWalk : earlier=visited.1.flatMap fun v => EdgeRoundStorage.roundCode raw mode ready.trials v.input.weights v.tape := by
        simp only [earlier,FramedEdgeRoundLayout.sourceRounds,parsed,FramedEdgeRoundLayout.rounds,readyPlan]
        rfl
      have visits : visited.1.length ≤ beforeCopies.eval x :=
        (visit_count raw mode ready.trials visited.1).trans (exactWalk ▸ count)
      have original : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ :=
        (ChargedSourceAssembly.edge_value source).trans ((PhysicalSourceInputJoin.edge_value source).symm.trans parsed)
      have base : n ≤ x := (ChargedSourceAssembly.edge_dimensions original).1.trans (Nat.le_add_right _ _)
      have bound : ready.trials ≤ trials.eval x := trialBound parsed κ
      have padded : n+ready.trials ≤ pad.eval x := by
        simp only [pad,eval_add,eval_X]
        exact Nat.add_le_add base bound
      let model (v : LiteralRoundSchedule.Visit (lineSize n)) (c : Code) :=
        EdgePackedRoundLayout.Model raw mode ready.trials v.input.weights v.tape c
      have each (v : LiteralRoundSchedule.Visit (lineSize n)) : ∃ c, model v c ∧
          fresh c ≤ roundCells.eval (pad.eval x) ∧ c.length ≤ roundCopies.eval (pad.eval x) := by
        obtain ⟨c,run,used,events⟩ := roundBound raw mode ready.trials v.input.weights v.tape
        exact ⟨c,run,used.trans (eval_mono roundCells padded),events.trans (eval_mono roundCopies padded)⟩
      obtain ⟨parts,path,used,events⟩ := collect model visited.1 (roundCells.eval (pad.eval x))
        (roundCopies.eval (pad.eval x)) (fun v _ => each v)
      refine ⟨parts.flatten,?_,?_,?_⟩
      · simp only [readyPlan]
        exact ⟨parts,rfl,path⟩
      · simp only [afterCells,eval_mul,eval_comp]
        exact used.trans (Nat.mul_le_mul_right _ visits)
      · simp only [afterCopies,eval_mul,eval_comp]
        exact events.trans (Nat.mul_le_mul_right _ visits)
  obtain ⟨roundCode,model,newSpace,newWork⟩ := extra
  let code := first++roundCode
  have stored : fresh code ≤ cells.eval x := by
    simpa only [code,fresh_append,cells,eval_add] using Nat.add_le_add space newSpace
  have size : code.length ≤ copies.eval x := by
    simpa only [code,List.length_append,copies,eval_add] using Nat.add_le_add work newWork
  refine ⟨prefixCode,roundCode,reached,model,stored,size,fun start => ?_⟩
  obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout code start
  have fits : (start+fresh code).size ≤ (start+cells.eval x).size := Nat.size_le_size (Nat.add_le_add_left stored start)
  exact ⟨same,paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
    fun block member offset inside => (widths block member offset inside).trans fits⟩

end DirectedFlowCutGap.FramedEdgePackedLayout
