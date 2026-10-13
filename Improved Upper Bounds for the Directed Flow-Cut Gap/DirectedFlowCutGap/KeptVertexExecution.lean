import DirectedFlowCutGap.KeptVertexEndpoints

namespace DirectedFlowCutGap.KeptVertex
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def keepSteps (s t u : Bits) (zero : Bool) : ℕ := if zero then bitSteps s t u zero+2 else 4
def keepCells (s t u : Bits) (zero : Bool) : ℕ := if zero then bitCells s t u zero else 1

theorem keep_return {heap : NaturalHeap} {word context : ℕ} {s t u : Bits} {zero : Bool}
    (hu : BoolList heap word u) (hc : Context heap context s t zero)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 80) (stack : List (Frame ℕ 80)) (source : Bits) :
    ∃ ext root,ext.length=keepCells s t u zero ∧ NaturalRun program (keepSteps s t u zero)
      (state heap next word context c d (⟨pc,.r3,saved⟩::stack) source 50) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (bit s t u zero)) := by
  obtain ⟨ep,sr,tr,flag,hp,he,hs,ht,hf⟩ := hc
  let frames := ⟨pc,.r3,saved⟩::stack
  have first : tickNatural program (state heap next word context c d frames source 50)=
      some ⟨state heap next word context c flag frames source 51,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have branch : tickNatural program (state heap next word context c flag frames source 51)=
      some ⟨state heap next word context c flag frames source (if zero then 52 else 70),[],0⟩ := by
    cases zero <;> simp [tickNatural,program,state,Registers.get,hf,tagBranch]
  cases zero with
  | false =>
    refine ⟨[.flag true],next,rfl,?_,by simp [bit,hn]⟩
    exact .step first (.step branch (flag_return true heap next word context c flag saved pc stack source))
  | true =>
    obtain ⟨ext,root,len,run,rep⟩ := endpoint_return hu ⟨ep,sr,tr,flag,hp,he,hs,ht,hf⟩
      next c flag hn saved pc stack source
    refine ⟨ext,root,len,?_,?_⟩
    · convert NaturalRun.step first (.step branch run) using 1 <;> simp [keepSteps]
    · have sameBit : bit s t u true=endpoint s t u := by
        cases h : same u s <;> simp [bit,endpoint,h]
      rwa [sameBit]

theorem keep_steps_bound (s t u : Bits) (zero : Bool) :
    keepSteps s t u zero+1 ≤ 32*(s.length+t.length+u.length+2)+1 := by
  have a := BinaryComparisonProgram.steps_bound u s
  have b := BinaryComparisonProgram.steps_bound u t
  cases zero <;> cases he : same u s <;> simp_all [keepSteps,bitSteps,secondSteps] <;> omega
end DirectedFlowCutGap.KeptVertex
