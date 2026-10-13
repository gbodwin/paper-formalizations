import DirectedFlowCutGap.KeptVertexFinish

namespace DirectedFlowCutGap.KeptVertex
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def secondSteps (s t u : Bits) (_zero : Bool) : ℕ :=
  if same u s then 3 else BinaryComparisonProgram.steps u t+7+3
def secondCells (s t u : Bits) (_zero : Bool) : ℕ :=
  if same u s then 1 else BinaryComparisonProgram.cells u t+1
def bitSteps (s t u : Bits) (zero : Bool) : ℕ :=
  BinaryComparisonProgram.steps u s+6+secondSteps s t u zero
def bitCells (s t u : Bits) (zero : Bool) : ℕ :=
  1+BinaryComparisonProgram.cells u s+secondCells s t u zero

theorem second_return {heap : NaturalHeap} {word context scratch tag : ℕ} {s t u : Bits}
    {zero : Bool} (hu : BoolList heap word u) (hc : Context heap context s t zero)
    (hscratch : heap[scratch]?=some (.pair word context))
    (htag : heap[tag]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u s)))
    (next b : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 80) (stack : List (Frame ℕ 80)) (source : Bits) :
    ∃ ext root,ext.length=secondCells s t u zero ∧ NaturalRun program (secondSteps s t u zero)
      (state heap next word b scratch tag (⟨pc,.r3,saved⟩::stack) source 56) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (endpoint s t u)) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  have branch : tickNatural program (state heap next word b scratch tag frames source 56)=
      some ⟨state heap next word b scratch tag frames source (if same u s then 70 else 57),[],0⟩ := by
    cases h : BinaryComparisonProgram.order u s <;>
      simp [tickNatural,program,state,Registers.get,htag,h,tagBranch,same,
        SupportRecoveryProgram.same,BinaryComparisonProgram.tag]
  by_cases h : same u s=true
  · simp only [h,ite_true] at branch
    exact ⟨[.flag true],next,by simp [secondCells,h],by
      simpa [secondSteps,h] using NaturalRun.step branch
        (flag_return true heap next word b scratch tag saved pc stack source),by simp [endpoint,h,hn]⟩
  · obtain ⟨d,sr,tr,flag,hp,hd,hsource,htarget,he⟩ := hc
    obtain ⟨e1,out,len1,cmp,tagout⟩ := compare_return hu htarget next scratch tag hn
      ⟨word,tr,scratch,tag⟩ 61 frames source
    let e2 : NaturalHeap := [.flag (same u t)]
    have len2 : e2.length=1 := rfl
    have tail := finish_return tagout (next+e1.length) word tr scratch saved pc stack source
    have outflag : ((heap++e1)++e2)[next+e1.length]?=some (.flag (same u t)) := by simp [e2,hn]
    let root := next+e1.length
    have t95 : tickNatural program (state heap next word b scratch tag frames source 57)=
        some ⟨state heap next word context scratch tag frames source 58,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hscratch]
    have t96 : tickNatural program (state heap next word context scratch tag frames source 58)=
        some ⟨state heap next word d scratch tag frames source 59,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t97 : tickNatural program (state heap next word d scratch tag frames source 59)=
        some ⟨state heap next word tr scratch tag frames source 60,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hd]
    have t98 : tickNatural program (state heap next word tr scratch tag frames source 60)=
        some ⟨state heap next word tr scratch tag
          (⟨61,.r3,⟨word,tr,scratch,tag⟩⟩::frames) source 48,[],0⟩ := by
      simp [tickNatural,program,state]
    simp only [h] at branch
    refine ⟨e1++e2,root,by simp [secondCells,h,len1,len2],?_,?_⟩
    · convert NaturalRun.step branch (.step t95 (.step t96 (.step t97 (.step t98
        (run_append cmp tail))))) using 1 <;> simp [secondSteps,h,List.append_assoc,state,e2,root]
      all_goals omega
    · simpa [endpoint,h,List.append_assoc] using outflag

theorem endpoint_return {heap : NaturalHeap} {word context : ℕ} {s t u : Bits}
    {zero : Bool} (hu : BoolList heap word u) (hc : Context heap context s t zero)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 80) (stack : List (Frame ℕ 80)) (source : Bits) :
    ∃ ext root,ext.length=bitCells s t u zero ∧ NaturalRun program (bitSteps s t u zero)
      (state heap next word context c d (⟨pc,.r3,saved⟩::stack) source 52) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (endpoint s t u)) := by
  obtain ⟨dr,sr,tr,flag,hp,hd,hsource,htarget,he⟩ := hc
  have hc' : Context heap context s t zero := ⟨dr,sr,tr,flag,hp,hd,hsource,htarget,he⟩
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair word context]
  obtain ⟨e1,tag,len1,cmp,htag⟩ := compare_return (boolList_extend hu e0)
    (boolList_extend hsource e0) (next+1) next d (by simp [e0,hn])
    ⟨word,sr,next,d⟩ 56 frames source
  obtain ⟨e2,root,len2,tail,out⟩ := second_return (boolList_extend hu (e0++e1))
    (context_extend hc' (e0++e1))
    (show (heap++(e0++e1))[next]?=some (.pair word context) from by simp [e0,hn])
    (by simpa [List.append_assoc] using htag)
    (next+1+e1.length) sr (by simp [e0,hn];omega) saved pc stack source
  have t90 : tickNatural program (state heap next word context c d frames source 52)=
      some ⟨state (heap++e0) (next+1) word context next d frames source 53,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e0]
  have t91 : tickNatural program (state (heap++e0) (next+1) word context next d frames source 53)=
      some ⟨state (heap++e0) (next+1) word dr next d frames source 54,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp e0]
  have t92 : tickNatural program (state (heap++e0) (next+1) word dr next d frames source 54)=
      some ⟨state (heap++e0) (next+1) word sr next d frames source 55,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hd e0]
  have t93 : tickNatural program (state (heap++e0) (next+1) word sr next d frames source 55)=
      some ⟨state (heap++e0) (next+1) word sr next d
        (⟨56,.r3,⟨word,sr,next,d⟩⟩::frames) source 48,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨e0++e1++e2,root,by simp [bitCells,e0,len1,len2];omega,?_,?_⟩
  · have all := NaturalRun.step t90 (.step t91 (.step t92 (.step t93
      (run_append cmp (by simpa [List.append_assoc] using tail)))))
    convert all using 1 <;> simp [bitSteps,e0,state]
    all_goals omega
  · simpa [List.append_assoc] using out

end DirectedFlowCutGap.KeptVertex
