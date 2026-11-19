import DirectedFlowCutGap.EpochGridTableProgram
import DirectedFlowCutGap.ActiveDemandListProgram
import DirectedFlowCutGap.EncodedTapeMaterialization

/-! Connect the split physical draw batch to the retained epoch input. -/

namespace DirectedFlowCutGap.PhysicalEpochInputData

open BinaryArithmetic RetainedGridState
open PhysicalEpochDraws (permutationValues cellValues values epochBounds)
open PhysicalDrawSequenceProgram (batch)
open EpochPermutationProgram (indices)

theorem cell_values_ofFn (L m : ℕ) (cells : FiniteGridSampler.Cells L m) :
    cellValues L m cells=List.ofFn (fun i => (FiniteGridSampler.cellsDecode L m cells i).val) := by
  have run : cellValues L m cells=((FiniteGridSampler.cellsRun L m cells).1).map Fin.val := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rcases cells with ⟨c,cs⟩
      simp [cellValues,FiniteGridSampler.cellsRun,ih]
  rw [run,FiniteGridSampler.cellsRun_list,List.map_ofFn]
  rfl

theorem cell_values_length (L m : ℕ) (cells : FiniteGridSampler.Cells L m) : (cellValues L m cells).length=m := by
  rw [cell_values_ofFn,List.length_ofFn]

theorem split_draws {n L : ℕ} (a : PairFlags n) (positive : 0<L) (fuel : ℕ) (source : Bits)
    (t : RetainedTapeInput.Tape L a) (rest : Bits) (reads : ℕ)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet a))))
      source=some (t,(rest,reads))) :
    let m := Fintype.card ↥(remainingSet a)
    let out := batch fuel (epochBounds L positive m) source
    indices (out.draws.take m)=permutationValues m t.1 ∧
      indices (out.draws.drop m)=cellValues L m t.2 ∧
      (out.draws.drop m).length=m ∧ out.suffix=rest ∧ out.requests.length=reads := by
  let m := Fintype.card ↥(remainingSet a)
  let out := batch fuel (epochBounds L positive m) source
  have whole := PhysicalEpochDraws.epoch_run fuel L m positive source
  rw [sample] at whole
  change some (values L m t,(rest,reads)) =
    (if out.requests.length ≤ source.length then some (indices out.draws,(out.suffix,0+out.requests.length)) else none) at whole
  by_cases enough : out.requests.length ≤ source.length
  · rw [ite_eq_left enough] at whole
    have root := Option.some.inj whole
    have both : indices out.draws=permutationValues m t.1++cellValues L m t.2 :=
      (congrArg Prod.fst root).symm
    have restEq := (congrArg Prod.snd root).symm
    have permLength := EpochPermutationData.valid_length (EpochPermutationData.values_valid m t.1)
    have htake : indices (out.draws.take m)=permutationValues m t.1 := by
      change (out.draws.take m).map (fun d => value d.index)=_
      rw [List.map_take,
        show out.draws.map (fun d => value d.index)=indices out.draws from rfl,both]
      exact List.take_left' permLength
    have hdrop : indices (out.draws.drop m)=cellValues L m t.2 := by
      change (out.draws.drop m).map (fun d => value d.index)=_
      rw [List.map_drop,show out.draws.map (fun d => value d.index)=indices out.draws from rfl,both]
      exact List.drop_left' permLength
    have size := congrArg List.length hdrop
    simp only [indices,List.length_map,cell_values_length] at size
    exact ⟨htake,hdrop,size,congrArg Prod.fst restEq,by simpa only [Nat.zero_add] using congrArg Prod.snd restEq⟩
  · rw [ite_eq_right enough] at whole
    contradiction

theorem active_at {n : ℕ} (a : PairFlags n) (i : Fin (Fintype.card ↥(remainingSet a))) :
    (RetainedTapeInput.activeEnum a i).val =
      (RetainedTapeInput.activeList a)[i.val]'(by rw [RetainedTapeInput.activeList_length]; exact i.isLt) := rfl

theorem materialized_order {n L : ℕ} (a : PairFlags n) (positive : 0<L) (t : RetainedTapeInput.Tape L a) :
    (RetainedTapeInput.materialize positive a t).order =
      (FinitePermutationSampler.run (Fintype.card ↥(remainingSet a)) t.1).order.map (fun i =>
        (RetainedTapeInput.activeList a)[i.val]'(by rw [RetainedTapeInput.activeList_length]; exact i.isLt)) := by
  change (FinitePermutationSampler.labelOrder (RetainedTapeInput.activeEnum a) t.1).map Subtype.val = _
  simp only [FinitePermutationSampler.labelOrder,FinitePermutationSampler.labelRun,FinitePermutationSampler.enumerate_list,
    List.map_map,Function.comp_def]
  exact List.map_congr_left (fun i _ => active_at a i)

theorem materialized_cells {n L : ℕ} (a : PairFlags n) (positive : 0<L) (t : RetainedTapeInput.Tape L a)
    (i : Fin (Fintype.card ↥(remainingSet a))) :
    let p := (RetainedTapeInput.activeEnum a i).val
    (cellValues L (Fintype.card ↥(remainingSet a)) t.2)[i.val]'(by rw [cell_values_length]; exact i.isLt) =
      ((RetainedTapeInput.materialize positive a t).cell p).val := by
  dsimp only
  let entry := RetainedTapeInput.activeEnum a i
  have h := RetainedTapeInput.materialize_cell positive a t entry.val entry.property
  have index : i.val<(cellValues L (Fintype.card ↥(remainingSet a)) t.2).length := by
    rw [cell_values_length]
    exact i.isLt
  have peek : (cellValues L (Fintype.card ↥(remainingSet a)) t.2)[i.val]? =
      some ((FiniteGridSampler.cellsDecode L (Fintype.card ↥(remainingSet a)) t.2) i).val := by
    rw [cell_values_ofFn]
    simp only [List.getElem?_ofFn,dite_eq_left i.isLt]
  rw [List.getElem?_eq_getElem index] at peek
  rw [Option.some.inj peek,h]
  change ((FiniteGridSampler.cellsDecode L (Fintype.card ↥(remainingSet a)) t.2) i).val =
    ((FiniteGridSampler.cellsDecode L (Fintype.card ↥(remainingSet a)) t.2) ((RetainedTapeInput.activeEnum a).symm entry)).val
  rw [show (RetainedTapeInput.activeEnum a).symm entry=i from Equiv.symm_apply_apply _ _]

private theorem outcome_width (bound : Bits) (fuel : ℕ) (tape : Bits) :
    (PhysicalBoundedDrawProgram.outcome bound fuel tape).index.length ≤ bound.length := by
  induction fuel generalizing tape with
  | zero => simp [PhysicalBoundedDrawProgram.outcome]
  | succ fuel ih =>
    rw [PhysicalBoundedDrawProgram.outcome]
    split
    · exact ih _
    · simp [PhysicalFairWordProgram.digits_length]

theorem batch_widths (fuel : ℕ) (limits : List Bits) (tape : Bits) {W : ℕ}
    (widths : ∀ word ∈ limits,word.length≤W) :
    ∀ d ∈ (batch fuel limits tape).draws,d.index.length≤W := by
  induction limits generalizing tape with
  | nil => simp [batch]
  | cons word rest ih =>
    intro d mem
    change d ∈ PhysicalBoundedDrawProgram.outcome word fuel tape ::
      (batch fuel rest (PhysicalBoundedDrawProgram.outcome word fuel tape).suffix).draws at mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact (outcome_width word fuel tape).trans (widths word (by simp))
    · exact ih _ (fun w hw => widths w (List.mem_cons_of_mem _ hw)) d later

theorem successful_tape_fits {n L : ℕ} (a : PairFlags n) (positive : 0<L) (fuel : ℕ) (source : Bits)
    (t : RetainedTapeInput.Tape L a) (rest : Bits) (reads : ℕ)
    (sample : EncodedSolverBits.run (LazyFairBitTrees.lower fuel
      (RetainedDrawTrees.tape L positive (Fintype.card ↥(remainingSet a)))) source=some (t,(rest,reads))) :
    (batch fuel (RetainedEpochFromMasks.bounds a positive) source).requests.length ≤ source.length := by
  let m := Fintype.card ↥(remainingSet a)
  let out := batch fuel (RetainedEpochFromMasks.bounds a positive) source
  have full := PhysicalEpochDraws.epoch_run fuel L m positive source
  rw [sample] at full
  change some (values L m t,(rest,reads)) =
    (if out.requests.length ≤ source.length then some (indices out.draws,(out.suffix,0+out.requests.length)) else none) at full
  change out.requests.length ≤ source.length
  by_contra missing
  rw [ite_eq_right missing] at full
  contradiction

private theorem permutation_prefix (fuel m : ℕ) (post : List Bits) (tape : Bits) :
    EpochPermutationData.Valid
      (indices ((batch fuel ((PhysicalEpochDraws.permutationBounds m).map (fun b => b.val.bits)++post) tape).draws.take m)) m := by
  induction m generalizing tape with
  | zero => exact .nil
  | succ m ih =>
    let out := PhysicalBoundedDrawProgram.outcome (m+1).bits fuel tape
    let raw := (PhysicalEpochDraws.permutationBounds m).map (fun b => b.val.bits)++post
    have index : value out.index < m+1 := by
      have h := PhysicalBoundedDrawProgram.index_lt (m+1).bits fuel tape (by rw [value_bits]; omega)
      simpa only [value_bits,out] using h
    change EpochPermutationData.Valid (value out.index::indices ((batch fuel raw out.suffix).draws.take m)) (m+1)
    exact .cons index (ih out.suffix)

private theorem batch_length (fuel : ℕ) (bounds : List Bits) (tape : Bits) :
    (batch fuel bounds tape).draws.length=bounds.length := by
  induction bounds generalizing tape with
  | nil => rfl
  | cons b bs ih => simp [batch,ih]

theorem permutation_valid {n L : ℕ} (a : PairFlags n) (positive : 0<L) (fuel : ℕ) (tape : Bits) :
    let m := Fintype.card ↥(remainingSet a)
    let out := batch fuel (RetainedEpochFromMasks.bounds a positive) tape
    EpochPermutationData.Valid (indices (out.draws.take m)) m := by
  let m := Fintype.card ↥(remainingSet a)
  let caps := (PhysicalEpochDraws.cellBounds L positive m).map (fun b => b.val.bits)
  simpa only [RetainedEpochFromMasks.bounds,PhysicalEpochDraws.epochBounds,List.map_append,m,caps] using
    permutation_prefix fuel m caps tape

theorem grid_length {n L : ℕ} (a : PairFlags n) (positive : 0<L) (fuel : ℕ) (tape : Bits) :
    let m := Fintype.card ↥(remainingSet a)
    ((batch fuel (RetainedEpochFromMasks.bounds a positive) tape).draws.drop m).length=m := by
  have each (m : ℕ) : (PhysicalEpochDraws.permutationBounds m).length=m := by
    induction m with
    | zero => rfl
    | succ m ih => simp [PhysicalEpochDraws.permutationBounds,ih]
  simp [List.length_drop,batch_length,RetainedEpochFromMasks.bounds,PhysicalEpochDraws.epochBounds,
    PhysicalEpochDraws.cellBounds,each]

end DirectedFlowCutGap.PhysicalEpochInputData
