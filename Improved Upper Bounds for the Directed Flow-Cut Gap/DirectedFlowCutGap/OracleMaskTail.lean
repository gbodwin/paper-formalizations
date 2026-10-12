import DirectedFlowCutGap.OracleTailMembership

namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def finishSteps (t u : Bits) (es : List (Bits × Bits)) : ℕ :=
  if same u t then 3 else memberSteps u es+6
def finishCells (t u : Bits) (es : List (Bits × Bits)) : ℕ :=
  if same u t then 1 else memberCells u es

theorem context_extend {heap : NaturalHeap} {p : ℕ} {s t : Bits} {es : List (Bits × Bits)}
    (h : Context heap p s t es) (extra : NaturalHeap) : Context (heap++extra) p s t es := by
  obtain ⟨d,e,sr,tr,hp,hd,hs,ht,he⟩ := h
  exact ⟨d,e,sr,tr,lookup_extend hp extra,lookup_extend hd extra,
    boolList_extend hs extra,boolList_extend ht extra,edgeList_extend he extra⟩

theorem false_return (heap : NaturalHeap) (next a b c d : ℕ) (saved : Registers ℕ)
    (pc : Fin 160) (stack : List (Frame ℕ 160)) (source : Bits) :
    NaturalRun program 2
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 110) []
      (state (heap++[.flag false]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have first : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 110)=
      some ⟨state (heap++[.flag false]) (next+1) a b c next
        (⟨pc,.r3,saved⟩::stack) source 111,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
  have last : tickNatural program (state (heap++[.flag false]) (next+1) a b c next
      (⟨pc,.r3,saved⟩::stack) source 111)=
      some ⟨state (heap++[.flag false]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact .step first (.step last (.done _))

theorem finish_return {heap : NaturalHeap} {word context scratch tag : ℕ} {s t u : Bits}
    {es : List (Bits × Bits)} (hu : BoolList heap word u) (hc : Context heap context s t es)
    (hscratch : heap[scratch]?=some (.pair word context))
    (htag : heap[tag]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u t)))
    (next a b : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 160) (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root,ext.length=finishCells t u es ∧ NaturalRun program (finishSteps t u es)
      (state heap next a b scratch tag (⟨pc,.r3,saved⟩::stack) source 99) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (if same u t then false else member u es)) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  have branch : tickNatural program (state heap next a b scratch tag frames source 99)=
      some ⟨state heap next a b scratch tag frames source (if same u t then 110 else 100),[],0⟩ := by
    cases h : BinaryComparisonProgram.order u t <;>
      simp [tickNatural,program,state,Registers.get,htag,h,tagBranch,same,
        SupportRecoveryProgram.same,BinaryComparisonProgram.tag]
  by_cases h : same u t=true
  · simp only [h,ite_true] at branch
    exact ⟨[.flag false],next,by simp [finishCells,h],by
      simpa [finishSteps,h] using NaturalRun.step branch (false_return heap next a b scratch tag saved pc stack source),
      by simp [h,hn]⟩
  · obtain ⟨d,edges,sr,tr,hp,hd,hsource,htarget,he⟩ := hc
    obtain ⟨ext,root,len,body,out⟩ := member_return he hu next scratch tag hn
      ⟨edges,word,scratch,tag⟩ 104 frames source
    have t100 : tickNatural program (state heap next a b scratch tag frames source 100)=
        some ⟨state heap next context b scratch tag frames source 101,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hscratch]
    have t101 : tickNatural program (state heap next context b scratch tag frames source 101)=
        some ⟨state heap next edges b scratch tag frames source 102,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t102 : tickNatural program (state heap next edges b scratch tag frames source 102)=
        some ⟨state heap next edges word scratch tag frames source 103,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hscratch]
    have t103 : tickNatural program (state heap next edges word scratch tag frames source 103)=
        some ⟨state heap next edges word scratch tag
          (⟨104,.r3,⟨edges,word,scratch,tag⟩⟩::frames) source 60,[],0⟩ := by
      simp [tickNatural,program,state]
    have t104 : tickNatural program (state (heap++ext) (next+ext.length) edges word scratch root frames source 104)=
        some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    simp only [h] at branch
    refine ⟨ext,root,by simpa [finishCells,h] using len,?_,by simpa [h] using out⟩
    convert NaturalRun.step branch (.step t100 (.step t101 (.step t102 (.step t103
      (run_append body (.step t104 (.done _))))))) using 1 <;> simp [finishSteps,h]

end DirectedFlowCutGap.OracleMask
