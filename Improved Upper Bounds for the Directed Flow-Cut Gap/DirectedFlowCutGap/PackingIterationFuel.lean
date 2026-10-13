import DirectedFlowCutGap.PackingIterationCounterCall

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

set_option maxRecDepth 10000 in
theorem fuel_prefix {heap : NaturalHeap} {context input fuelRoot : ℕ} {fuel : Bits}
    (pair : heap[context]?=some (.pair input fuelRoot)) (table : BoolList heap fuelRoot fuel)
    (next cap original d : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ ext cursor, ext.length=1+BinaryCounterProgram.cells fuel ∧
      NaturalRun program (BinaryCounterProgram.steps fuel+8)
        (state heap next cap original context d [] source 4820) []
        (state (heap++ext) (next+ext.length) cap original cursor input [] source 4830) ∧
      IndexSpine (heap++ext) cursor (value fuel) := by
  let heap₁ := heap++[.pair cap context]
  have base : heap₁[next]?=some (.pair cap context) := by simp [heap₁,dense]
  have context₁ : heap₁[context]?=some (.pair input fuelRoot) := lookup_extend pair [.pair cap context]
  obtain ⟨ext,cursor,len,body,rep⟩ := counter_return (boolList_extend table [.pair cap context])
    (next+1) original context next (by simp [dense]) ⟨fuelRoot,original,context,next⟩ 4823 [] source
  have base₂ := lookup_extend base ext
  have context₂ := lookup_extend context₁ ext
  have t0 : tickNatural program (state heap next cap original context d [] source 4820)=
      some ⟨state heap₁ (next+1) cap original context next [] source 4821,[],0⟩ := by
    have slot : program 4820=.make .r3 (.pair .r0 .r2) 4821 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,heap₁]
  have t1 : tickNatural program (state heap₁ (next+1) cap original context next [] source 4821)=
      some ⟨state heap₁ (next+1) fuelRoot original context next [] source 4822,[],0⟩ := by
    have slot : program 4821=.field .r0 .r2 true 4822 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,context₁]
  have t2 : tickNatural program (state heap₁ (next+1) fuelRoot original context next [] source 4822)=
      some ⟨state heap₁ (next+1) fuelRoot original context next
        [⟨4823,.r2,⟨fuelRoot,original,context,next⟩⟩] source 4817,[],0⟩ := by
    have slot : program 4822=.call 4817 4823 .r2 := rfl
    simp [tickNatural,state,slot]
  have t3 : tickNatural program (state (heap₁++ext) (next+1+ext.length) fuelRoot original cursor next [] source 4823)=
      some ⟨state (heap₁++ext) (next+1+ext.length) cap original cursor next [] source 4824,[],0⟩ := by
    have slot : program 4823=.field .r0 .r3 false 4824 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,base₂]
  have t4 : tickNatural program (state (heap₁++ext) (next+1+ext.length) cap original cursor next [] source 4824)=
      some ⟨state (heap₁++ext) (next+1+ext.length) cap original cursor context [] source 4825,[],0⟩ := by
    have slot : program 4824=.field .r3 .r3 true 4825 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,base₂]
  have t5 : tickNatural program (state (heap₁++ext) (next+1+ext.length) cap original cursor context [] source 4825)=
      some ⟨state (heap₁++ext) (next+1+ext.length) cap original cursor input [] source 4830,[],0⟩ := by
    have slot : program 4825=.field .r3 .r3 false 4830 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,context₂]
  refine ⟨[.pair cap context]++ext,cursor,by simp [len,Nat.add_comm],?_,?_⟩
  · have finish := run_append body (.step t3 (.step t4 (.step t5 (.done _))))
    convert NaturalRun.step t0 (.step t1 (.step t2 finish)) using 1 <;>
      simp [heap₁,List.append_assoc,Nat.add_assoc]
    simp [Nat.add_comm]
  · simpa [heap₁,List.append_assoc] using rep
end DirectedFlowCutGap.PackingIteration
