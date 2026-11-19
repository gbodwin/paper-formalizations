import DirectedFlowCutGap.CandidateConfiguredCutProgram

/-!
# Decode candidate numerators by counting threshold flags

The thresholds for a point occupy a contiguous block in numerical label
order. A closed block has one included flag for each level up to the
decoded maximum, including zero. The difference of the two block counts
equals the retained numerator for an unremoved core vertex.
-/

namespace DirectedFlowCutGap.CandidateMaskNumeratorData

open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open CandidateEnumeration (Point Node Network pointIndex nodeIndex networkIndex)
open CandidatePhysicalCut (networkSize numberEquiv outputMask problem)
open CandidatePortDifferenceSystem CandidateClosureProvider
open EncodedCandidateCapacity (Input)
open MinimumClosureCut (source sink cores)

noncomputable def maskOf {n L : ℕ} (X : Finset (Network n L)) : Bits :=
  (List.finRange (networkSize n L)).map fun v => decide ((numberEquiv n L).symm v ∈ X)

def block {n : ℕ} (L : ℕ) (flags : Bits) (point : Point n) : Bits :=
  (flags.drop (pointIndex point*(L+1))).take (L+1)

theorem block_value {n L : ℕ} (X : Finset (Network n L)) (p : Point n) :
    block L (maskOf X) p = (List.finRange (L+1)).map fun j => decide ((.inl (p,j) : Network n L) ∈ X) := by
  let start := pointIndex p*(L+1)
  have h := CandidateEnumeration.pointIndex_lt p
  have enough : start+(L+1)≤networkSize n L := by
    have room := Nat.mul_le_mul_right (L+1) (Nat.succ_le_of_lt h)
    unfold networkSize
    simpa only [start,Nat.succ_mul] using room.trans (Nat.le_add_right _ 2)
  have available : L+1≤networkSize n L-start := by omega
  apply List.ext_getElem
  · simp [block,maskOf,← show start=pointIndex p*(L+1) from rfl,Nat.min_eq_left available]
  · intro i hi hj
    have hiL : i<L+1 := by simpa using hj
    have inside : start+i<networkSize n L := by omega
    let j : Fin (L+1) := ⟨i,hiL⟩
    let v : Fin (networkSize n L) := ⟨start+i,inside⟩
    have index : numberEquiv n L (.inl (p,j))=v := by
      apply Fin.ext
      exact CandidatePhysicalCut.numberEquiv_value (.inl (p,j))
    simp only [block,List.getElem_take,List.getElem_drop,maskOf,List.getElem_map,List.getElem_finRange]
    change decide ((numberEquiv n L).symm v ∈ X)=decide ((.inl (p,j) : Network n L) ∈ X)
    rw [← index,Equiv.symm_apply_apply]

private theorem count_levels {L : ℕ} (q : Fin (L+1)) :
    ((List.finRange (L+1)).map (fun j => decide (j≤q))).count true=q.val+1 := by
  let levels := (List.finRange (L+1)).filter (fun j => decide (j≤q))
  have listCount : ((List.finRange (L+1)).map (fun j => decide (j≤q))).count true=levels.length := by
    simp [List.count_eq_length_filter,List.filter_map,levels,Function.comp_def]
  have intact : levels.Nodup := (List.nodup_finRange _).filter _
  have card := List.toFinset_card_of_nodup intact
  have asInterval : levels.toFinset=Finset.Iic q := by
    ext j
    simp [levels]
  rw [listCount,← card,asInterval]
  exact Fin.card_Iic _

def numerator {n : ℕ} (D : Input n) (L : ℕ) (flags : Bits) (v : Fin n) : ℕ :=
  if D.removed[v.val] then L else
    (block L flags (TerminalPorts.core v,true)).count true-
      (block L flags (TerminalPorts.core v,false)).count true

theorem numerators_eq {n : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L)) :
    ((List.finRange n).map fun v => (v,(numerator D L (outputMask D s t L B EN E) v : ℤ))) =
      (EncodedCandidateOutput.solve D s t L B EN E (ResidualSearch.Enumeration.fin n)).numerators := by
  let S := system D.graph s t D.cut L B
  let costs := integerCosts D.cut
  let P := problem D s t L B
  let chosen := (ClosureRuntime.solve P E).1
  have closed : P.IsClosed chosen := (ClosureRuntime.solve_optimal P E
    (closure_nonempty S costs
      (system_nonempty D.graph s t D.cut L B positive feasible))).1
  let decoded := CandidateThresholdClosure.decode S costs chosen closed
  let counted := CountedFlow.solve (D.construct s t L B EN E).cells E source sink (D.construct s t L B EN E).budget
  have ref : cores counted.asSet=chosen :=
    (EncodedCandidateOutput.coreScan_set counted).symm.trans (EncodedCandidateOutput.solved_cores_value D s t L B EN E)
  have bits (p : Point n) : (block L (outputMask D s t L B EN E) p).count true=(decoded p).val+1 := by
    change (block L (maskOf counted.asSet) p).count true=(decoded p).val+1
    rw [block_value]
    have included (j : Fin (L+1)) : ((.inl (p,j) : Network n L) ∈ counted.asSet) ↔ j≤decoded p := by
      have eq : ((.inl (p,j) : Network n L) ∈ counted.asSet) ↔ (p,j) ∈ chosen := by
        rw [← ref]
        simp [MinimumClosureCut.core]
      rw [eq,← CandidateThresholdClosure.encode_decode S costs chosen closed, CandidateThresholdClosure.mem_encode]
    have flags : (fun j : Fin (L+1) => decide ((.inl (p,j) : Network n L) ∈ counted.asSet)) =
        (fun j : Fin (L+1) => decide (j≤decoded p)) := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,included]
    rw [flags]
    exact count_levels (decoded p)
  have ascending (v : Fin n) : (decoded (TerminalPorts.core v,false)).val ≤ (decoded (TerminalPorts.core v,true)).val := by
    let a : Point n := (TerminalPorts.core v,false)
    let b : Point n := (TerminalPorts.core v,true)
    have ok := (CandidateThresholdClosure.decode_feasible S costs chosen closed).2 a b
    have nonpos : S.bound a b≤0 := by
      apply (min_le_left _ _).trans
      simp [orderBound,a,b]
    have h := ok.trans nonpos
    change ((decoded a).val : ℤ)-(decoded b).val≤0 at h
    change (decoded a).val ≤ (decoded b).val
    omega
  rw [EncodedCandidateOutput.solve_value D s t L B positive EN E (ResidualSearch.Enumeration.fin n) feasible]
  change _ = (List.finRange n).map fun v => (v,if v ∈ D.cut then (L : ℤ) else
    ((decoded (TerminalPorts.core v,true)).val : ℤ)-(decoded (TerminalPorts.core v,false)).val)
  apply List.map_congr_left
  intro v _
  simp only [numerator,Input.mem_cut]
  by_cases removed : D.removed[v.val]=true
  · simp [removed]
  · simp only [removed,Bool.false_eq_true,ite_false,bits,Prod.mk.injEq,true_and]
    have bound := ascending v
    omega

end DirectedFlowCutGap.CandidateMaskNumeratorData
