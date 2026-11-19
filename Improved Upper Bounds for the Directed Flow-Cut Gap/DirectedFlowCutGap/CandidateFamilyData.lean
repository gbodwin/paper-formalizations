import DirectedFlowCutGap.CandidateFamilyProgram

/-! Identify the physical family with the exact retained optimizer's rows. -/

namespace DirectedFlowCutGap.CandidateFamilyData

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow CandidateClosureProvider
open EncodedCandidateCapacity (Input)
open CandidatePortDifferenceSystem (candidateClosure)
open CandidateEnumeration (Node Network)
open CandidateDemandRowProgram (rowWords)
open CandidateFamilyScanProgram (selectedRow)
open CandidateFamilyProgram (Shared StateAt)
open RetainedMassTableProgram (TableAt DataRows pairOrder)
open GraphWalkExtension (EdgeList)
open EpochActiveFromMaskProgram (labelPair)

noncomputable def familyWords {n L : ℕ} (D : Input n) (active : PairFlags n) (B : ℕ) (grid : Bits)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L)) : List (List Bits) :=
  (pairOrder n).map (selectedRow D active B grid EN E)

theorem active_feasible {n L : ℕ} (D : Input n) {demands : Finset (Pair n)} (s : Code D.graph demands L)
    (removed : D.cut=cutSet s.data.cut) (p : Pair n) (active : flag s.data.remaining p=true) :
    CandidateFeasible D.graph p.1 p.2 D.cut L (4*s.data.scale) := by
  rw [removed]
  exact current_feasible_data s p (membership_of_flag s p active)

set_option maxHeartbeats 1300000 in
theorem row_values {n L : ℕ} (D : Input n) (p : Pair n) (B : ℕ) (grid : Bits) (gridValue : value grid=L)
    (positive : 0<L) (feasible : CandidateFeasible D.graph p.1 p.2 D.cut L B)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L)) :
    (rowWords D p L B grid EN E).map value = (List.finRange n).map (fun v =>
      (candidateNumerator D.graph p.1 p.2 D.cut L B positive
        (finiteHooks (candidateClosure D.graph p.1 p.2 D.cut L B) E) feasible v).toNat) := by
  have h := CandidateNumeratorScanProgram.scan_candidate_values D p.1 p.2 L B positive feasible EN E grid gridValue
  change (rowWords D p L B grid EN E).map (fun x => (value x : ℤ)) = _ at h
  rw [EncodedCandidateOutput.solve_finiteHooks D p.1 p.2 L B positive EN E (ResidualSearch.Enumeration.fin n) feasible] at h
  simpa [List.map_map,Function.comp_def,ResidualSearch.Enumeration.fin,ResidualSearch.Enumeration.ofEquiv,List.finRange] using
    congrArg (List.map Int.toNat) h

private theorem numerator_cut {n L : ℕ} (D : Input n) (p : Pair n) (B : ℕ) (positive : 0<L)
    (E : ResidualSearch.Enumeration (Network n L)) {X Y : Finset (Fin n)} (same : X=Y)
    (left : CandidateFeasible D.graph p.1 p.2 X L B) (right : CandidateFeasible D.graph p.1 p.2 Y L B) (v : Fin n) :
    candidateNumerator D.graph p.1 p.2 X L B positive (finiteHooks (candidateClosure D.graph p.1 p.2 X L B) E) left v =
    candidateNumerator D.graph p.1 p.2 Y L B positive (finiteHooks (candidateClosure D.graph p.1 p.2 Y L B) E) right v := by
  subst Y
  rfl

theorem family_data {n L : ℕ} (D : Input n) {demands : Finset (Pair n)} (s : Code D.graph demands L)
    (removed : D.cut=cutSet s.data.cut) (grid : Bits) (gridValue : value grid=L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L)) :
    DataRows (buildFamily (tabulatedOptimizer positive (ResidualSearch.Enumeration.fin n) E) s)
      (familyWords D s.data.remaining (4*s.data.scale) grid EN E) := by
  let Q := tabulatedOptimizer (G:=D.graph) (D:=demands) positive (ResidualSearch.Enumeration.fin n) E
  have atPair (p : Pair n) : (selectedRow D s.data.remaining (4*s.data.scale) grid EN E p).map value =
      (row (buildFamily Q s) p).toList := by
    by_cases hp : flag s.data.remaining p=true
    · have feasible := active_feasible D s removed p hp
      have valueEq := row_values D p (4*s.data.scale) grid gridValue positive feasible EN E
      have solved : (row (buildFamily Q s) p) = tabulatedRow positive (ResidualSearch.Enumeration.fin n) E s p
          (membership_of_flag s p hp) := by
        simp [row,buildFamily,hp,Q,tabulatedOptimizer]
      simp only [selectedRow,hp,ite_true,solved,valueEq,tabulatedRow,Vector.toList_ofFn,List.finRange,List.map_ofFn,
        Function.comp_def]
      apply congrArg List.ofFn
      funext v
      rw [ClosureRuntime.candidateNumerators_read]
      exact congrArg Int.toNat (numerator_cut D p (4*s.data.scale) positive E removed feasible _ v)
    · have inactive : flag s.data.remaining p=false := Bool.eq_false_of_not_eq_true hp
      simp [selectedRow,inactive,row,buildFamily,value]
  have aligned (ps : List (Pair n)) : List.Forall₂ (fun xs p => xs.map value=(row (buildFamily Q s) p).toList)
      (ps.map (selectedRow D s.data.remaining (4*s.data.scale) grid EN E)) ps := by
    induction ps with
    | nil => exact .nil
    | cons p ps ih => exact .cons (atPair p) ih
  exact aligned (pairOrder n)

private theorem word_width (k : ℕ) (flags grid : Bits) (b : Bool) :
    (CandidateNumeratorCellProgram.word k flags grid b).length ≤ max grid.length k.size := by
  cases b with
  | true => exact le_max_left _ _
  | false =>
    have cap : CandidateNumeratorCellProgram.secondCount k flags≤k :=
      List.count_le_length.trans (List.length_take_le _ _)
    change (CandidateNumeratorCellProgram.secondCount k flags-CandidateNumeratorCellProgram.firstCount k flags).bits.length≤_
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le_size ((Nat.sub_le _ _).trans cap)).trans (le_max_right _ _)

theorem family_width {n L : ℕ} (D : Input n) (a : PairFlags n) (B : ℕ) (grid : Bits)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L)) :
    ∀ row∈familyWords D a B grid EN E,∀ w∈row,w.length ≤ max grid.length (L+1).size := by
  intro row mem w member
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp mem
  unfold selectedRow at member
  split at member
  · change w∈CandidateNumeratorScanProgram.scan (L+1) grid (CandidatePhysicalCut.outputMask D p.1 p.2 L B EN E) D.removed.toList at member
    let flags := CandidatePhysicalCut.outputMask D p.1 p.2 L B EN E
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp member
    have k : i<D.removed.toList.length := by simpa [flags] using hi
    rw [CandidateNumeratorScanProgram.scan_get (L+1) grid flags D.removed.toList i k]
    exact word_width _ _ _ _
  · have eq := (List.mem_replicate.mp member).2
    simp [eq]

end DirectedFlowCutGap.CandidateFamilyData
