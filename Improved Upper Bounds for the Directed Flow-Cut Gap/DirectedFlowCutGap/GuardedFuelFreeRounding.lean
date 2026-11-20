import DirectedFlowCutGap.PaidTotalRawGraphExecution
import DirectedFlowCutGap.GuardedIntegerRoundingWorkBounds
import DirectedFlowCutGap.MaskBoundaryAssembly

/-! Reuse the exact packed inputs and output reader while erasing the fuel
calculation from the executed hard branch. -/
namespace DirectedFlowCutGap.GuardedFuelFreeRounding

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RetainedGridState (PairFlags)
open OriginalGraphCostEnvelope (preparedCells preparedCells_eq)
open PhysicalIntegerRounding (Result boundaryWords maskCopyCharge)
open RawGraphControllerProgram (instructionBound program)
open RawGraphInputStore (prepare)
open PhysicalCoverAccess (Read)
open CachedReferenceExecution (FastState)
open GuardedIntegerRoundingWork (collect readMask runPacked)

private theorem mask_copy_paid (n : ℕ) (bits : Bits) :
    (MaskBoundaryAssembly.run n bits).2 ≤ maskCopyCharge n n := by
  simpa only [maskCopyCharge,two_mul] using MaskBoundaryAssembly.paid n bits

private def collectMask {n : ℕ} (prepared boundary : ℕ)
    (execution : Option (FastState 26704) × ℕ) : Read (Result n) :=
  let work := prepared+execution.2
  match execution.1 with
  | none => (none,work+boundary)
  | some final =>
      let restored := readMask final
      let base := work+restored.2+boundary
      match restored.1 with
      | none => (none,base)
      | some bits =>
          let copy := MaskBoundaryAssembly.run n bits
          let paid := base+maskCopyCharge n n
          (some ⟨copy.1,final.source,paid⟩,base+max (maskCopyCharge n n) copy.2)

private theorem collectMask_eq {n : ℕ} (prepared boundary : ℕ)
    (execution : Option (FastState 26704) × ℕ)
    (width : ∀ out, execution.1=some out → ∀ bits, (readMask out).1=some bits → bits.length=n) :
    collectMask (n:=n) prepared boundary execution=collect prepared boundary 0 execution := by
  unfold collectMask collect
  cases reached : execution.1 with
  | none => simp only [Nat.add_zero]
  | some out =>
      cases seen : (readMask out).1 with
      | none => simp only [seen,Nat.add_zero]
      | some bits =>
          have mask : (MaskBoundaryAssembly.run n bits).1=PhysicalIntegerRounding.fromWord n bits :=
            MaskBoundaryAssembly.result_at n bits
          simp only [seen,Nat.add_zero,width out reached bits seen,mask,max_eq_left (mask_copy_paid n bits)]

private theorem collected_word {n : ℕ} (prepared boundary : ℕ)
    (execution : Option (FastState 26704) × ℕ) {cut : Result n}
    (done : (collectMask prepared boundary execution).1=some cut) :
    ∃ out bits, execution.1=some out ∧ (readMask out).1=some bits ∧ (MaskBoundaryAssembly.run n bits).1=cut.mask := by
  unfold collectMask at done
  cases run : execution.1 with
  | none => simp only [run,reduceCtorEq] at done
  | some out =>
    cases read : (readMask out).1 with
    | none => simp only [run,read,reduceCtorEq] at done
    | some bits =>
      simp only [run,read,Option.some.injEq] at done
      exact ⟨out,bits,rfl,read,congrArg Result.mask done⟩

private theorem reference_of_paid {C : ℕ} (p : Program C) (fuel : ℕ) (entry : BitState C)
    {out : FastState C} (done : (PaidGuardedExecution.execute p fuel (FastState.ofReference entry) 0).1=some out) :
    ∃ q, GuardedReferenceExecution.execute p fuel entry 0=some (out.freeze,q) := by
  let exec := PaidGuardedExecution.execute p fuel (FastState.ofReference entry) 0
  have paid := PaidGuardedExecution.observation p fuel (FastState.ofReference entry) 0
  change exec.1.map (fun u => (u,exec.2))=_ at paid
  have old := CachedGuardedReferenceExecution.execute_ofReference p fuel entry 0
  rw [← paid,done] at old
  exact ⟨exec.2,old.symm⟩

set_option maxHeartbeats 900000 in
private theorem returned_width {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} (initial : BitState 26704)
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L)
    (out : FastState 26704) (done : (PaidTotalRawGraphExecution.run initial data positive).1=some out)
    (bits : Bits) (seen : (readMask out).1=some bits) : bits.length=n := by
  rw [PaidTotalRawGraphExecution.run_eq] at done
  obtain ⟨_,done⟩ := reference_of_paid _ _ _ done
  let F := CandidateEnumeration.make n L
  let EN := F.nodes.enumeration
  let E := F.network.enumeration
  have declared := RawGraphControllerProgram.guarded_cut positive EN E initial
    data.bounded data.entry data.quiet data.dense data.graph data.trials
  cases result : ControllerTapeModel.run positive E (OriginalGraphControllerLaw.ratio n) (value trials)
      (OriginalGraphControllerLaw.epochs n) (OriginalGraphControllerLaw.epochs n)
      (PhysicalControllerInitializer.initialCode adj positive) initial.source with
  | none =>
      rw [result] at declared
      rw [declared _ _] at done
      cases done
  | some r =>
      rcases r with ⟨answer,suffix,reads⟩
      rw [result] at declared
      obtain ⟨refState,_,ref,mask,_,_,_,_,_⟩ := declared
      have same : out.freeze=refState := congrArg Prod.fst (Option.some.inj (done.symm.trans ref))
      have natural := (PhysicalCoverAccess.readWord_value out.freeze.heap out.freeze.registers.d).symm.trans
        ((congrArg Prod.fst (GuardedIntegerRoundingWork.readMask_eq out)).symm.trans seen)
      change PhysicalCoverReader.readWord (eraseState out.freeze).heap (eraseState out.freeze).registers.d=some bits at natural
      rw [same,mask] at natural
      rw [← Option.some.inj natural,Vector.length_toList]

private theorem input {n : ℕ} (adj : PairFlags n) (L T : ℕ) (tape : Bits) :
    let words := boundaryWords n L T
    let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
    let H := preparedCells n L T
    RawGraphControllerLaw.Input (L:=L) adj T.bits (H+1) H entry.1 := by
  dsimp only
  simp only [PhysicalIntegerRounding.boundary_dimension,PhysicalIntegerRounding.boundary_level,
    PhysicalIntegerRounding.boundary_trials]
  simpa only [preparedCells_eq adj L T] using (RawGraphInputStore.prepare_spec (L:=L) adj T.bits tape).1

def hard {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L) (tape : Bits) : Read (Result n) :=
  let words := boundaryWords n L T
  let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
  let run := PaidTotalRawGraphExecution.run entry.1 (input adj L T tape) positive
  collectMask entry.2 words.paid run

theorem hard_mask_copy {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L) (tape : Bits)
    {cut : Result n} (done : (hard T adj L positive tape).1=some cut) :
    ∃ bits, bits.length=n ∧ (MaskBoundaryAssembly.run n bits).1=cut.mask ∧
      (MaskBoundaryAssembly.run n bits).2 ≤ maskCopyCharge n n := by
  let words := boundaryWords n L T
  let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
  let data := input adj L T tape
  let execution := PaidTotalRawGraphExecution.run entry.1 data positive
  obtain ⟨out,bits,finish,read,mask⟩ := collected_word entry.2 words.paid execution done
  exact ⟨bits,returned_width entry.1 data positive out finish bits read,mask,mask_copy_paid n bits⟩

private theorem collect_control {n : ℕ} (prepared boundary fee : ℕ) (run : Option (FastState 26704) × ℕ) :
    collect (n:=n) prepared boundary fee run =
      ((collect (n:=n) prepared boundary 0 run).1,(collect (n:=n) prepared boundary 0 run).2+fee) := by
  unfold collect
  cases run.1 with
  | none => rfl
  | some out =>
      dsimp only
      cases (GuardedIntegerRoundingWork.readMask out).1 <;> rfl

private theorem compare_collect (n : ℕ) (entry : BitState 26704 × ℕ) (boundary amount : ℕ)
    (result : Option (FastState 26704) × ℕ)
    (value : result=PaidGuardedExecution.execute program amount (FastState.ofReference entry.1) 0) :
    let fresh := collect (n:=n) entry.2 boundary 0 result
    let old := runPacked n entry boundary amount
    fresh.1=old.1 ∧ fresh.2 ≤ old.2 := by
  let encoded := BinaryNaturalView.encode amount
  let ran := PaidGuardedExecution.executeBinary program encoded.1 (FastState.ofReference entry.1) 0
  have prior := (PaidGuardedExecution.binary_spec program encoded.1 (FastState.ofReference entry.1) 0).1
  rw [show BinaryArithmetic.value encoded.1=amount from BinaryNaturalView.encode_value _] at prior
  have asBinary : result=ran.1 := value.trans prior.symm
  change (collect (n:=n) entry.2 boundary 0 result).1=(collect (n:=n) entry.2 boundary (encoded.2+ran.2) ran.1).1 ∧
    (collect (n:=n) entry.2 boundary 0 result).2 ≤ (collect (n:=n) entry.2 boundary (encoded.2+ran.2) ran.1).2
  rw [asBinary,collect_control entry.2 boundary (encoded.2+ran.2) ran.1]
  exact ⟨rfl,Nat.le_add_right _ _⟩

theorem meets_old_entry {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L) (tape : Bits) :
    let fresh := hard T adj L positive tape
    let old := GuardedIntegerRoundingWork.hard T adj L tape
    fresh.1=old.1 ∧ fresh.2 ≤ old.2 := by
  let words := boundaryWords n L T
  let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
  let amount := instructionBound n L (preparedCells n L T+1) T.bits+1
  let result := PaidTotalRawGraphExecution.run entry.1 (input adj L T tape) positive
  change (collectMask (n:=n) entry.2 words.paid result).1=(runPacked n entry words.paid amount).1 ∧
    (collectMask (n:=n) entry.2 words.paid result).2≤(runPacked n entry words.paid amount).2
  rw [collectMask_eq _ _ _ (returned_width entry.1 (input adj L T tape) positive)]
  exact compare_collect n entry words.paid amount result (PaidTotalRawGraphExecution.run_eq entry.1 (input adj L T tape) positive)

theorem hard_value {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L) (tape : Bits) :
    (hard T adj L positive tape).1=PhysicalIntegerRounding.hardRun T adj L tape :=
  (meets_old_entry T adj L positive tape).1.trans (GuardedIntegerRoundingWork.hard_value T adj L tape)

theorem hard_paid {n T L : ℕ} (adj : PairFlags n) (positive : 0<L) (tape : Bits) :
    (hard T adj L positive tape).2 ≤ GuardedIntegerRoundingWork.budget n L T :=
  (meets_old_entry T adj L positive tape).2.trans (GuardedIntegerRoundingWork.hard_paid adj tape)

end DirectedFlowCutGap.GuardedFuelFreeRounding
