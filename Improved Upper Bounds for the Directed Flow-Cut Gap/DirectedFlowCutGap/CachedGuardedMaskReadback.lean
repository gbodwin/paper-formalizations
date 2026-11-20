import DirectedFlowCutGap.CachedWordRead
import DirectedFlowCutGap.GuardedIntegerRoundingWorkBounds
import DirectedFlowCutGap.PaidTotalRawGraphExecution

/-! The mask readback of the actual raw packed run uses the measured binary
reader. A returned state contains the full original mask. Tape exhaustion
returns before any mask readback. -/
namespace DirectedFlowCutGap.CachedGuardedMaskReadback

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RetainedGridState (PairFlags)
open RawGraphControllerProgram (program instructionBound)
open CachedReferenceExecution (FastState)
open GuardedIntegerRoundingWork (readMask)

def measure (s : FastState 26704) : CachedWordRead.Counted Bits :=
  CachedWordRead.word s.store s.store.cells.size s.registers.d

theorem measured_value (s : FastState 26704) : (measure s).1=readMask s :=
  CachedWordRead.word_eq s.store s.store.cells.size s.registers.d

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
/-- The returned pointer refers to the exact cut of the original controller. -/
theorem returned_word {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} (initial : BitState 26704)
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L)
    (out : FastState 26704) (done : (PaidTotalRawGraphExecution.run initial data positive).1=some out) :
    ∃ bits, (measure out).1.1=some bits ∧ bits.length=n := by
  rw [PaidTotalRawGraphExecution.run_eq] at done
  obtain ⟨_,done⟩ := reference_of_paid _ _ _ done
  let F := CandidateEnumeration.make n L
  let EN := F.nodes.enumeration
  let E := F.network.enumeration
  have verified := RawGraphControllerProgram.guarded_cut positive EN E initial
    data.bounded data.entry data.quiet data.dense data.graph data.trials
  cases result : ControllerTapeModel.run positive E (OriginalGraphControllerLaw.ratio n) (value trials)
      (OriginalGraphControllerLaw.epochs n) (OriginalGraphControllerLaw.epochs n)
      (PhysicalControllerInitializer.initialCode adj positive) initial.source with
  | none =>
      rw [result] at verified
      rw [verified _ _] at done
      cases done
  | some r =>
      rcases r with ⟨answer,suffix,reads⟩
      rw [result] at verified
      obtain ⟨refState,_,ref,mask,_,_,_,_,_⟩ := verified
      have same : out.freeze=refState := congrArg Prod.fst (Option.some.inj (done.symm.trans ref))
      have natural := (congrArg Prod.fst (GuardedIntegerRoundingWork.readMask_eq out)).trans
        (PhysicalCoverAccess.readWord_value out.freeze.heap out.freeze.registers.d)
      change (readMask out).1=PhysicalCoverReader.readWord (eraseState out.freeze).heap (eraseState out.freeze).registers.d at natural
      rw [same,mask] at natural
      rw [measured_value]
      exact ⟨_,natural,Vector.length_toList⟩

def work (result : Option (FastState 26704)) : ℕ :=
  (result.map fun out => (measure out).2).getD 0

theorem raw_paid {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} (initial : BitState 26704)
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    let fuel := instructionBound n L H trials+1
    work (PaidTotalRawGraphExecution.run initial data positive).1 ≤
      (H+fuel)*(2*CachedWordRead.loadBudget (H+fuel) (A+fuel)) := by
  let fuel := instructionBound n L H trials+1
  cases found : (PaidTotalRawGraphExecution.run initial data positive).1 with
  | none => exact Nat.zero_le _
  | some out =>
      obtain ⟨bits,seen,_⟩ := returned_word initial data positive out found
      have ran := found
      rw [PaidTotalRawGraphExecution.run_eq] at ran
      have original : (FastState.ofReference initial).freeze.Bounded H A := by
        rw [CachedReferenceExecution.freeze_ofReference]
        exact data.bounded
      have fits : out.freeze.Bounded (H+fuel) (A+fuel) :=
        PaidGuardedExecution.returned_bounded program fuel (FastState.ofReference initial) 0 original ran
      have cells := fits.1
      simp only [State.records,FastState.freeze,Array.length_toList] at cells
      have store : out.store.cells.size≤H+fuel := by omega
      have pointers := fits.2.2.1
      have d := fits.2.2.2.1.2.2.2
      have paid := CachedWordRead.word_paid store pointers out.store.cells.size d seen
      exact paid.trans (Nat.mul_le_mul_right _ store)

end DirectedFlowCutGap.CachedGuardedMaskReadback
