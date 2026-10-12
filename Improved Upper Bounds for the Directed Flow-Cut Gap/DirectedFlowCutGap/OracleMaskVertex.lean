import DirectedFlowCutGap.OracleMaskTail

namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def secondSteps (s t u : Bits) (es : List (Bits × Bits)) : ℕ :=
  if same u s then 3 else BinaryComparisonProgram.steps u t+7+finishSteps t u es
def secondCells (s t u : Bits) (es : List (Bits × Bits)) : ℕ :=
  if same u s then 1 else BinaryComparisonProgram.cells u t+finishCells t u es
def bitSteps (s t u : Bits) (es : List (Bits × Bits)) : ℕ :=
  BinaryComparisonProgram.steps u s+6+secondSteps s t u es
def bitCells (s t u : Bits) (es : List (Bits × Bits)) : ℕ :=
  1+BinaryComparisonProgram.cells u s+secondCells s t u es

theorem second_return {heap : NaturalHeap} {word context scratch tag : ℕ} {s t u : Bits}
    {es : List (Bits × Bits)} (hu : BoolList heap word u) (hc : Context heap context s t es)
    (hscratch : heap[scratch]?=some (.pair word context))
    (htag : heap[tag]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u s)))
    (next b : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 160) (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root,ext.length=secondCells s t u es ∧ NaturalRun program (secondSteps s t u es)
      (state heap next word b scratch tag (⟨pc,.r3,saved⟩::stack) source 94) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (bit s t u es)) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  have branch : tickNatural program (state heap next word b scratch tag frames source 94)=
      some ⟨state heap next word b scratch tag frames source (if same u s then 110 else 95),[],0⟩ := by
    cases h : BinaryComparisonProgram.order u s <;>
      simp [tickNatural,program,state,Registers.get,htag,h,tagBranch,same,
        SupportRecoveryProgram.same,BinaryComparisonProgram.tag]
  by_cases h : same u s=true
  · simp only [h,ite_true] at branch
    exact ⟨[.flag false],next,by simp [secondCells,h],by
      simpa [secondSteps,h] using NaturalRun.step branch
        (false_return heap next word b scratch tag saved pc stack source),by simp [bit,h,hn]⟩
  · obtain ⟨d,edges,sr,tr,hp,hd,hsource,htarget,he⟩ := hc
    have hc' : Context heap context s t es := ⟨d,edges,sr,tr,hp,hd,hsource,htarget,he⟩
    obtain ⟨e1,out,len1,cmp,tagout⟩ := compare_return hu htarget next scratch tag hn
      ⟨word,tr,scratch,tag⟩ 99 frames source
    obtain ⟨e2,root,len2,tail,outflag⟩ := finish_return (boolList_extend hu e1)
      (context_extend hc' e1) (lookup_extend hscratch e1) tagout
      (next+e1.length) word tr (by simp [hn]) saved pc stack source
    have t95 : tickNatural program (state heap next word b scratch tag frames source 95)=
        some ⟨state heap next word context scratch tag frames source 96,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hscratch]
    have t96 : tickNatural program (state heap next word context scratch tag frames source 96)=
        some ⟨state heap next word d scratch tag frames source 97,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t97 : tickNatural program (state heap next word d scratch tag frames source 97)=
        some ⟨state heap next word tr scratch tag frames source 98,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hd]
    have t98 : tickNatural program (state heap next word tr scratch tag frames source 98)=
        some ⟨state heap next word tr scratch tag
          (⟨99,.r3,⟨word,tr,scratch,tag⟩⟩::frames) source 48,[],0⟩ := by
      simp [tickNatural,program,state]
    simp only [h] at branch
    refine ⟨e1++e2,root,by simp [secondCells,h,len1,len2],?_,?_⟩
    · convert NaturalRun.step branch (.step t95 (.step t96 (.step t97 (.step t98
        (run_append cmp tail))))) using 1 <;> simp [secondSteps,h,List.append_assoc,state]
      all_goals omega
    · simpa [bit,h,List.append_assoc] using outflag

theorem bit_return {heap : NaturalHeap} {word context : ℕ} {s t u : Bits}
    {es : List (Bits × Bits)} (hu : BoolList heap word u) (hc : Context heap context s t es)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 160) (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root,ext.length=bitCells s t u es ∧ NaturalRun program (bitSteps s t u es)
      (state heap next word context c d (⟨pc,.r3,saved⟩::stack) source 90) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (bit s t u es)) := by
  obtain ⟨dr,edges,sr,tr,hp,hd,hsource,htarget,he⟩ := hc
  have hc' : Context heap context s t es := ⟨dr,edges,sr,tr,hp,hd,hsource,htarget,he⟩
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair word context]
  obtain ⟨e1,tag,len1,cmp,htag⟩ := compare_return (boolList_extend hu e0)
    (boolList_extend hsource e0) (next+1) next d (by simp [e0,hn])
    ⟨word,sr,next,d⟩ 94 frames source
  obtain ⟨e2,root,len2,tail,out⟩ := second_return (boolList_extend hu (e0++e1))
    (context_extend hc' (e0++e1))
    (show (heap++(e0++e1))[next]?=some (.pair word context) from by simp [e0,hn])
    (by simpa [List.append_assoc] using htag)
    (next+1+e1.length) sr (by simp [e0,hn];omega) saved pc stack source
  have t90 : tickNatural program (state heap next word context c d frames source 90)=
      some ⟨state (heap++e0) (next+1) word context next d frames source 91,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e0]
  have t91 : tickNatural program (state (heap++e0) (next+1) word context next d frames source 91)=
      some ⟨state (heap++e0) (next+1) word dr next d frames source 92,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp e0]
  have t92 : tickNatural program (state (heap++e0) (next+1) word dr next d frames source 92)=
      some ⟨state (heap++e0) (next+1) word sr next d frames source 93,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hd e0]
  have t93 : tickNatural program (state (heap++e0) (next+1) word sr next d frames source 93)=
      some ⟨state (heap++e0) (next+1) word sr next d
        (⟨94,.r3,⟨word,sr,next,d⟩⟩::frames) source 48,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨e0++e1++e2,root,by simp [bitCells,e0,len1,len2];omega,?_,?_⟩
  · have all := NaturalRun.step t90 (.step t91 (.step t92 (.step t93
      (run_append cmp (by simpa [List.append_assoc] using tail)))))
    convert all using 1 <;> simp [bitSteps,e0,state]
    all_goals omega
  · simpa [List.append_assoc] using out

end DirectedFlowCutGap.OracleMask
