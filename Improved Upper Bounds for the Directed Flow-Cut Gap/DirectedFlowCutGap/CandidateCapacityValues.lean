import DirectedFlowCutGap.CandidateCapacityWords
import DirectedFlowCutGap.CandidateTerminalFlagsProgram

/-!
# Numeric interfaces for constructing candidate capacities

The stored index tests recover equality of ports and points. The threshold
test and the capacity words retain the exact original closure predicates
and fit the width used by the physical cut solver.
-/

namespace DirectedFlowCutGap.CandidateCapacityValues

open BinaryArithmetic CandidateEnumeration
open EncodedCandidateCapacity (Input)

theorem match_labels {α : Type} [DecidableEq α] {index : α→ℕ}
    (injective : Function.Injective index) (a b : α) (x y : Bits)
    (hx : value x=index a) (hy : value y=index b) :
    CandidateLevelTestProgram.answer false x y [] = decide (a=b) := by
  apply Bool.eq_iff_iff.mpr
  rw [CandidateLevelTestProgram.answer_spec,decide_eq_true_eq,hx,hy]
  simp [value,injective.eq_iff]

theorem match_ports {n : ℕ} (a b : Port n) (x y : Bits)
    (hx : value x=portIndex a) (hy : value y=portIndex b) :
    CandidateLevelTestProgram.answer false x y [] = decide (a=b) :=
  match_labels portIndex_injective a b x y hx hy

theorem match_points {n : ℕ} (a b : Point n) (x y : Bits)
    (hx : value x=pointIndex a) (hy : value y=pointIndex b) :
    CandidateLevelTestProgram.answer false x y [] = decide (a=b) :=
  match_labels pointIndex_injective a b x y hx hy

theorem threshold_matches {n : ℕ} (D : Input n) (L B : ℕ) (a b : Node n L)
    (x y shifted : Bits) (hx : value x=a.2.val) (hy : value y=b.2.val)
    (hs : value shifted=CandidateCapacityFlags.shift D L B a.1 b.1) :
    CandidateLevelTestProgram.answer (decide (a.1=b.1)) x y shifted =
      CandidateCapacityFlags.barrierFlag D L B a b := by
  apply Bool.eq_iff_iff.mpr
  rw [CandidateLevelTestProgram.answer_spec,hx,hy,hs]
  simp only [CandidateCapacityFlags.barrierFlag,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]

private theorem normal_bits_of_nat (k : ℕ) : Normal k.bits := by
  have h := trim_spec k.bits
  have e := normal_bits h.1
  rw [h.2.1,value_bits] at e
  rw [e]
  exact h.1

theorem capacity_word {n : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ) (a b : Network n L) :
    let fields := CandidateCapacityFlags.flags D s t L B a b
    CandidateCapacityWords.word (CandidatePhysicalCut.fuelWord D s t L B) fields.1 fields.2 =
      (CandidatePhysicalCut.capacities D s t L B (CandidatePhysicalCut.numberEquiv n L a)
        (CandidatePhysicalCut.numberEquiv n L b)).bits := by
  let fields := CandidateCapacityFlags.flags D s t L B a b
  change CandidateCapacityWords.word (CandidatePhysicalCut.fuelWord D s t L B) fields.1 fields.2 = _
  have canonical : Normal (CandidatePhysicalCut.fuelWord D s t L B) := normal_bits_of_nat _
  rw [CandidateCapacityWords.canonical canonical]
  exact congrArg Nat.bits (CandidateCapacityFlags.amount_eq_capacity D s t L B a b)

theorem word_width {n : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ) (unit hard : Bool) :
    (CandidateCapacityWords.word (CandidatePhysicalCut.fuelWord D s t L B) unit hard).length ≤
      CandidatePhysicalCut.capacityWidth n L := by
  have canonical : Normal (CandidatePhysicalCut.fuelWord D s t L B) := normal_bits_of_nat _
  rw [CandidateCapacityWords.canonical canonical,Nat.size_eq_bits_len]
  apply Nat.size_le_size
  have hf : value (CandidatePhysicalCut.fuelWord D s t L B)≤CandidatePhysicalCut.budgetCap n L := by
    rw [CandidatePhysicalCut.fuelWord,value_bits]
    simpa only [CandidatePhysicalCut.problem,Fintype.card_fin] using
      CandidateClosureProvider.candidate_budget_le D.graph s t D.cut L B
  have hn : 0<n := Nat.zero_lt_of_lt s.isLt
  have positive : 0<CandidatePhysicalCut.budgetCap n L := by
    unfold CandidatePhysicalCut.budgetCap
    positivity
  cases unit <;> cases hard <;> simp only [CandidateCapacityFlags.amount,Bool.false_eq_true,ite_true,ite_false] <;> omega

end DirectedFlowCutGap.CandidateCapacityValues
