import DirectedFlowCutGap.GuardedIntegerRoundingWorkBounds
namespace DirectedFlowCutGap.GuardedIntegerRoundingWork

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RetainedGridState (PairFlags)
open PhysicalIntegerRounding (Result boundaryWords fromWord maskCopyCharge)
open RawGraphInputStore (prepare cells)
open RawGraphControllerProgram (program instructionBound)
open OriginalGraphCostEnvelope (preparedCells preparedCells_eq packedCost)
open PhysicalCoverAccess (Read)
open CachedReferenceExecution (FastState)

open Polynomial in
theorem hard_polynomial : ∃ p : Polynomial ℕ, ∀ n L T, L ≤ n → budget n L T ≤ p.eval (n+T) := by
  obtain ⟨p,packs⟩ := OriginalGraphCostEnvelope.bounded_trials_polynomial
  let cells : Polynomial ℕ := 16*(X+1)^2+p
  let width : Polynomial ℕ := cells+1
  let guard : ℕ := GuardedReferenceExecution.guardCost 26704
  let instruction : ℕ := controlCost 26704+128
  refine ⟨p+128*cells*width^2+PhysicalIntegerRoundingCost.boundaryBudget X X X+
    p*(C instruction*width^2+C guard)+16*(X+cells+1)^2+40*(p+1)^2,?_⟩
  intro n L T inside
  let x := n+T
  let g := p.eval x
  let limit := 16*(x+1)^2+g
  let H := preparedCells n L T
  let work := instructionBound n L (H+1) T.bits
  let fuel := work+1
  have base : packedCost n L T ≤ g := packs n L T inside
  have fuel_le : fuel ≤ g := by
    have h : (1 : ℕ) ≤ guard := by decide
    have costs : fuel*guard ≤ packedCost n L T := by
      unfold packedCost RawGraphControllerProgram.chargeBound
      dsimp only
      exact (Nat.le_add_left _ _).trans (Nat.le_add_left _ _)
    exact ((by simpa only [Nat.mul_one] using Nat.mul_le_mul_left fuel h : fuel ≤ fuel*guard).trans costs).trans base
  have count : H+1 ≤ 16*(x+1)^2 := by
    have bits (k : ℕ) : k.bits.length ≤ k := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    unfold H preparedCells x
    nlinarith [bits n,bits L,bits T,Nat.zero_le (n*T),sq_nonneg T]
  have heap : H+1+fuel ≤ limit := Nat.add_le_add count fuel_le
  have addr : H+fuel ≤ limit := by omega
  have reads : PhysicalIntegerRoundingCost.readBound n L T ≤ 128*limit*(limit+1)^2 := by
    change PhysicalCoverAccess.wordBound (H+1+fuel) (H+fuel) ≤ _
    unfold PhysicalCoverAccess.wordBound PhysicalCoverAccess.cellBound
    calc
      _ ≤ limit*(64*(limit+1)*(limit+1)+64*(limit+1)*(limit+1)) := by gcongr
      _ = _ := by ring
  have boundary : PhysicalIntegerRoundingCost.boundaryBudget n L T ≤
      PhysicalIntegerRoundingCost.boundaryBudget x x x := by
    have hn : n ≤ x := Nat.le_add_right _ _
    have ht : T ≤ x := Nat.le_add_left _ _
    have hl := inside.trans hn
    unfold PhysicalIntegerRoundingCost.boundaryBudget
    gcongr
  have steps : PaidGuardedExecution.budget 26704 (H+1) H fuel ≤ g*(instruction*(limit+1)^2+guard) := by
    change fuel*(instruction*(H+1+fuel+1)*(H+fuel+1)+guard) ≤ _
    have mult : instruction*(H+1+fuel+1)*(H+fuel+1) ≤ instruction*(limit+1)^2 := by
      rw [pow_two,Nat.mul_assoc]
      exact Nat.mul_le_mul_left instruction
        (Nat.mul_le_mul (Nat.add_le_add_right heap 1) (Nat.add_le_add_right addr 1))
    exact Nat.mul_le_mul fuel_le (Nat.add_le_add_right mult guard)
  have controls : 40*(fuel+1)^2 ≤ 40*(g+1)^2 := by gcongr
  have copy : maskCopyCharge n (H+1+fuel) ≤ 16*(x+limit+1)^2 := by
    unfold maskCopyCharge
    have hn : n ≤ x := Nat.le_add_right _ _
    gcongr
  simp only [cells,width,PhysicalIntegerRoundingCost.boundaryBudget,eval_add,eval_mul,eval_pow,
    eval_ofNat,eval_C,eval_X,eval_one]
  change packedCost n L T+PaidGuardedExecution.budget 26704 (H+1) H fuel+
    PhysicalIntegerRoundingCost.boundaryBudget n L T+PhysicalIntegerRoundingCost.readBound n L T+
    maskCopyCharge n (H+1+fuel)+40*(fuel+1)^2 ≤
    g+128*limit*(limit+1)^2+PhysicalIntegerRoundingCost.boundaryBudget x x x+
    g*(instruction*(limit+1)^2+guard)+16*(x+limit+1)^2+40*(g+1)^2
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    base steps) boundary) reads) copy) controls).trans_eq (by ac_rfl)

end DirectedFlowCutGap.GuardedIntegerRoundingWork
