import DirectedFlowCutGap.GuardedIntegerRoundingWork
import DirectedFlowCutGap.PhysicalIntegerRoundingCost

namespace DirectedFlowCutGap.GuardedIntegerRoundingWork

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RetainedGridState (PairFlags)
open PhysicalIntegerRounding (boundaryWords maskCopyCharge)
open RawGraphInputStore (prepare cells)
open RawGraphControllerProgram (program instructionBound)
open OriginalGraphCostEnvelope (preparedCells preparedCells_eq packedCost)
open PhysicalCoverAccess (Read)
open CachedReferenceExecution (FastState)

attribute [local irreducible] RawGraphControllerProgram.instructionBound RawGraphInputStore.prepare
  RawGraphControllerProgram.program RawGraphInputStore.cells BinaryNaturalView.encode

private theorem word_paid (x : ℕ) : (BinaryNaturalView.encode x).2 ≤ 16*(x+1)^2 :=
  (BinaryNaturalView.encode_paid x).trans (Nat.mul_le_mul_left 16
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.size_le.mpr Nat.lt_two_pow_self) 1) 2))

private theorem boundary_paid (n L T : ℕ) :
    (boundaryWords n L T).paid ≤ PhysicalIntegerRoundingCost.boundaryBudget n L T := by
  have hn := word_paid n
  have hl := word_paid L
  have ht := word_paid T
  unfold boundaryWords PhysicalIntegerRoundingCost.boundaryBudget
  dsimp only
  omega

private theorem encoded_execution {C : ℕ} (p : Program C) (fuel : ℕ) (s : FastState C) :
    let encoded := BinaryNaturalView.encode fuel
    let executed := PaidGuardedExecution.executeBinary p encoded.1 s 0
    executed.1=PaidGuardedExecution.execute p fuel s 0 ∧ encoded.2+executed.2 ≤ 40*(fuel+1)^2 := by
  dsimp only
  let encoded := BinaryNaturalView.encode fuel
  obtain ⟨same,control⟩ := PaidGuardedExecution.binary_spec p encoded.1 s 0
  have fv : value encoded.1=fuel := BinaryNaturalView.encode_value _
  rw [fv] at same control
  refine ⟨same,?_⟩
  have size : encoded.1.length ≤ fuel := by
    rw [show encoded.1=fuel.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have cost : encoded.2 ≤ 16*(fuel+1)^2 := word_paid fuel
  have controlPaid : (PaidGuardedExecution.executeBinary p encoded.1 s 0).2 ≤ 24*(fuel+1)^2 := by
    calc
      _ ≤ _ := control
      _ ≤ 24*(fuel+1)*(fuel+1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right size 1)
      _ = _ := by ring
  change encoded.2+(PaidGuardedExecution.executeBinary p encoded.1 s 0).2 ≤ _
  omega

private theorem read_paid {H B : ℕ} (s : FastState 26704) (fits : s.freeze.Bounded H B) :
    (readMask s).2 ≤ PhysicalCoverAccess.wordBound H B ∧ s.store.cells.size ≤ H := by
  have len : s.freeze.heap.length ≤ H := by
    have total := fits.1
    unfold State.records at total
    omega
  have reads := PhysicalCoverAccess.readWord_charge fits.2.2.1 fits.2.2.2.1.2.2.2
  refine ⟨?_,?_⟩
  · rw [readMask_eq]
    apply reads.trans
    unfold PhysicalCoverAccess.wordBound PhysicalCoverAccess.cellBound
    gcongr
  · simpa only [FastState.freeze,Array.length_toList] using len

private theorem prepare_paid {n : ℕ} (adj : PairFlags n) (L T : ℕ) (tape : Bits) :
    let words := boundaryWords n L T
    let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
    let H := preparedCells n L T
    (FastState.ofReference entry.1).freeze.Bounded (H+1) H ∧ entry.2 ≤ packedCost n L T := by
  dsimp only
  simp only [CachedReferenceExecution.freeze_ofReference,PhysicalIntegerRounding.boundary_dimension,
    PhysicalIntegerRounding.boundary_level,PhysicalIntegerRounding.boundary_trials]
  obtain ⟨data,packs⟩ := RawGraphInputStore.prepare_spec (L:=L) adj T.bits tape
  rw [preparedCells_eq adj L T] at data packs
  exact ⟨data.bounded,packs.trans (Nat.le_add_right _ _)⟩

private theorem runPacked_paid (n : ℕ) (entry : BitState 26704 × ℕ) (boundary fuel H B : ℕ)
    (fits : (FastState.ofReference entry.1).freeze.Bounded H B) :
    (runPacked n entry boundary fuel).2 ≤ entry.2+PaidGuardedExecution.budget 26704 H B fuel+
      boundary+PhysicalCoverAccess.wordBound (H+fuel) (B+fuel)+maskCopyCharge n (H+fuel)+40*(fuel+1)^2 := by
  let encoded := BinaryNaturalView.encode fuel
  let start := FastState.ofReference entry.1
  let executed := PaidGuardedExecution.executeBinary program encoded.1 start 0
  obtain ⟨same,control⟩ := encoded_execution program fuel start
  change executed.1=_ at same
  change encoded.2+executed.2 ≤ _ at control
  have machine : executed.1.2 ≤ PaidGuardedExecution.budget 26704 H B fuel := by
    rw [same]
    simpa only [Nat.zero_add] using PaidGuardedExecution.paid_le program fuel start 0 fits
  have limit (out : FastState 26704) (ran : executed.1.1=some out) :
      (readMask out).2 ≤ PhysicalCoverAccess.wordBound (H+fuel) (B+fuel) ∧ out.store.cells.size ≤ H+fuel := by
    rw [same] at ran
    exact read_paid out (PaidGuardedExecution.returned_bounded program fuel start 0 fits ran)
  have observed := collect_paid_le (n:=n) entry.2 boundary (encoded.2+executed.2) executed.1 _ _ limit
  refine observed.trans ?_
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add_left machine _) (Nat.le_refl _)) (Nat.le_refl _)) (Nat.le_refl _)) control

def budget (n L T : ℕ) : ℕ :=
  let H := preparedCells n L T
  let fuel := instructionBound n L (H+1) T.bits+1
  packedCost n L T+PaidGuardedExecution.budget 26704 (H+1) H fuel+
    PhysicalIntegerRoundingCost.boundaryBudget n L T+PhysicalIntegerRoundingCost.readBound n L T+
    maskCopyCharge n (H+1+fuel)+40*(fuel+1)^2

theorem hard_paid {n T L : ℕ} (adj : PairFlags n) (tape : Bits) :
    (hard T adj L tape).2 ≤ budget n L T := by
  let words := boundaryWords n L T
  let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
  let H := preparedCells n L T
  let fuel := instructionBound n L (H+1) T.bits+1
  obtain ⟨fits,packing⟩ := prepare_paid adj L T tape
  change (runPacked n entry words.paid fuel).2 ≤ _
  refine (runPacked_paid n entry words.paid fuel (H+1) H fits).trans ?_
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_right packing _) (boundary_paid n L T)) (Nat.le_refl _)) (Nat.le_refl _)) (Nat.le_refl _)

end DirectedFlowCutGap.GuardedIntegerRoundingWork
