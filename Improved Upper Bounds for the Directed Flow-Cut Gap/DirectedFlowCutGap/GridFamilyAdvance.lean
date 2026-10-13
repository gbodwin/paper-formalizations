import DirectedFlowCutGap.GridFamilyControlCalls

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
set_option maxRecDepth 32768

theorem advance_run {heap : NaturalHeap} {b c : ℕ} {exponent fuel : Bits}
    (exp : BoolList heap b exponent) (input : BoolList heap c fuel)
    (next a head : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ ext expRoot fuelRoot,NaturalRun program
      (BinaryIncrementProgram.steps exponent+BinaryPredecessorProgram.steps fuel+12)
      (state heap next a b c head stack source 10133) []
      (state (heap++ext) (next+ext.length) a expRoot fuelRoot head stack source 10135) ∧
      BoolList (heap++ext) expRoot (increment true exponent).1 ∧
      BoolList (heap++ext) fuelRoot (predecessor fuel).1 := by
  have t0 : tickNatural program (state heap next a b c head stack source 10133)=
      some ⟨state heap next a b c head (⟨10134,.r1,⟨a,b,c,head⟩⟩::stack) source 10104,[],0⟩ := by rfl
  obtain ⟨ei,er,ri,eiRep⟩ := increment_helper exp next a c head dense ⟨a,b,c,head⟩ 10134 stack source
  have t1 : tickNatural program
      (state (heap++ei) (next+ei.length) a er c head stack source 10134)=
      some ⟨state (heap++ei) (next+ei.length) a er c head
        (⟨10135,.r2,⟨a,er,c,head⟩⟩::stack) source 10107,[],0⟩ := by rfl
  obtain ⟨ep,fr,rp,fpRep⟩ := predecessor_helper (boolList_extend input ei) (next+ei.length)
    a er head (by simp [dense]) ⟨a,er,c,head⟩ 10135 stack source
  refine ⟨ei++ep,er,fr,?_,?_,?_⟩
  · have whole := NaturalRun.step t0 (run_append ri (.step t1 rp))
    convert whole using 1 <;> simp [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    all_goals omega
  · simpa [List.append_assoc] using boolList_extend eiRep ep
  · simpa [List.append_assoc] using fpRep
end DirectedFlowCutGap.GridFamily
