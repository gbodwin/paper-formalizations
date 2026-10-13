import DirectedFlowCutGap.AdaptivePackingWeightedData

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem actual_weights {n : ℕ} {heap : NaturalHeap} {frame cap original input : ℕ}
    {label : Fin n → Bits} {capacity : Row n} {s : BinaryFractionalCore.State n} {q : BinaryFractionalCore.Choice n}
    (data : SelectedData heap frame cap original input label capacity s q)
    (next flag : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext, ∃ out : NaturalState 4800,
    ∃ result : WeightedData out.heap out.registers.c cap original input label capacity s q,
      NaturalRun program (28+(1+(PackingUpdateRow.steps (get capacity q.bottleneck)
        capacity.toList s.weights.toList q.mask.toList+2+18)))
        (state heap next data.best data.cost frame flag stack source 4472) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=stack ∧ out.source=source ∧ out.pc=4519 ∧
      out.registers.a=result.selected.old.total ∧ out.registers.b=result.selected.amount ∧
      out.registers.d=result.bestFrame := by
  obtain ⟨mask,index,choiceCell,maskRep,_⟩ := data.choiceRep
  obtain ⟨pm,pa,pc,pw⟩ := candidate_weight_paths data.frameRep data.old.first choiceCell
  obtain ⟨e₁,l₁,r₁,bf,ctx⟩ := prepare_weights pm pa pc pw next data.best data.cost flag dense stack source
  let n₁ := next+3
  let d₁ := data.extend e₁
  obtain ⟨e₂,weights,l₂,r₂,weightsRep⟩ := weights_return (get capacity q.bottleneck)
    d₁.capacityRep d₁.old.weightsRep (boolList_extend maskRep e₁) d₁.amountRep ctx (by simp) (by simp)
    n₁ (next+1) (by simp [n₁,List.length_append,dense,l₁])
    ⟨cap,data.old.weights,next+2,next+1⟩ 4501 stack source
  rw [PackingUpdateRow.result_eq_update] at weightsRep
  have call : tickNatural program
      (state (heap++e₁) n₁ cap data.old.weights (next+2) (next+1) stack source 4500)=
      some ⟨state (heap++e₁) n₁ cap data.old.weights (next+2) (next+1)
        (⟨4501,.r0,⟨cap,data.old.weights,next+2,next+1⟩⟩::stack) source 4018,[],0⟩ := by
    have slot : program 4500=.call 4018 4501 .r0 := rfl
    simp [tickNatural,state,slot]
  let n₂ := n₁+e₂.length
  let d₂ := d₁.extend e₂
  have bf₂ := best_frame_extend bf e₂
  obtain ⟨pair,bcell,bestCell⟩ := bf₂
  have tp : HeapPath (heap++e₁++e₂) (next+1)
      [true,true,true,true,true,true,false,true,true,true,false] data.old.total :=
    .cons bcell (path_append (candidate_original_path d₂.frameRep) d₂.old.totalPath)
  have ap : HeapPath (heap++e₁++e₂) (next+1) [true,true,true,false] data.amount :=
    .cons bcell (path_extend (path_extend pa e₁) e₂)
  obtain ⟨e₃,l₃,r₃,wp⟩ := prepare_total tp ap n₂ weights data.old.weights (next+2)
    (by simp [n₂,n₁,List.length_append,dense,l₁,Nat.add_assoc]) stack source
  let h := heap++e₁++e₂++e₃
  let result : WeightedData h n₂ cap original input label capacity s q :=
    ⟨frame,next+1,weights,mask,index,d₂.extend e₃,wp,
      best_frame_extend ⟨pair,bcell,bestCell⟩ e₃,
      (by simpa [h,d₂,d₁,SelectedData.extend,List.append_assoc] using lookup_extend choiceCell (e₁++e₂++e₃)),
      (by simpa [h,List.append_assoc] using boolList_extend maskRep (e₁++e₂++e₃)),
      list_extend weightsRep e₃⟩
  let out := state h (n₂+1) data.old.total data.amount n₂ (next+1) stack source 4519
  refine ⟨e₁++e₂++e₃,out,result,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · convert run_append r₁ (.step call (run_append r₂ r₃)) using 1
    · omega
    · rfl
  · simp [out,h,state,List.append_assoc]
  · simp [out,state,n₂,n₁,List.length_append,l₁,l₃,Nat.add_assoc]
end DirectedFlowCutGap.AdaptivePackingState
