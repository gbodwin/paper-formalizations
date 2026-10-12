import DirectedFlowCutGap.GraphLookupCalls

/-! Equal labels follow the real retained-record selection branch; unequal
labels return the already computed suffix answer without touching its cost. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def lookupDecisionSteps (u : Bits) (x : Entry) (tail : Option Walk) : ℕ :=
  if BinaryComparisonProgram.order x.1 u=.eq then 4+lookupFinishSteps x.2 tail else 3

def lookupDecisionCells (u : Bits) (x : Entry) (tail : Option Walk) : ℕ :=
  if BinaryComparisonProgram.order x.1 u=.eq then lookupFinishCells x.2 tail else 0

theorem lookup_decision {heap : NaturalHeap} {head tail p d : ℕ} {x : Entry} {q : Option Walk} {u : Bits}
    (entry : GraphRelaxationProgram.StoredEntry heap head x) (rest : StoredOption heap tail q)
    (scratch : heap[p]?=some (.pair head tail))
    (tag : heap[d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order x.1 u)))
    (next a b : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=lookupDecisionCells u x q ∧
      NaturalRun program (lookupDecisionSteps u x q)
        (state heap next a b p d (⟨pc,.r3,saved⟩::stack) source 690) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root
        (if BinaryComparisonProgram.order x.1 u=.eq then GraphRelaxationProgram.pick x.2 q else q) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  have branch : tickNatural program (state heap next a b p d frames source 690)=
      some ⟨state heap next a b p d frames source
        (if BinaryComparisonProgram.order x.1 u=.eq then 691 else 712),[],0⟩ := by
    cases ho : BinaryComparisonProgram.order x.1 u <;>
      simp [tickNatural,program,state,Registers.get,tag,ho,BinaryComparisonProgram.tag,tagBranch]
  by_cases he : BinaryComparisonProgram.order x.1 u=.eq
  · obtain ⟨vertex,walk,hhead,_,rep⟩ := entry
    obtain ⟨ext,root,len,body,out⟩ := lookup_finish rep rest next p d hn saved pc stack source
    have t691 : tickNatural program (state heap next a b p d frames source 691)=
        some ⟨state heap next head b p d frames source 692,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t692 : tickNatural program (state heap next head b p d frames source 692)=
        some ⟨state heap next walk b p d frames source 693,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hhead]
    have t693 : tickNatural program (state heap next walk b p d frames source 693)=
        some ⟨state heap next walk tail p d frames source 694,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    simp only [he,ite_true] at branch
    exact ⟨ext,root,by simpa [lookupDecisionCells,he] using len,
      by
        convert (NaturalRun.step branch (.step t691 (.step t692 (.step t693 body)))) using 1 <;>
          simp [lookupDecisionSteps,he]
        omega,by simpa [he] using out⟩
  · have t712 : tickNatural program (state heap next a b p d frames source 712)=
        some ⟨state heap next a b p tail frames source 713,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t713 : tickNatural program (state heap next a b p tail frames source 713)=
        some ⟨state heap next saved.a saved.b saved.c tail stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    simp only [he,ite_false] at branch
    exact ⟨[],tail,by simp [lookupDecisionCells,he],
      by simpa [lookupDecisionSteps,he] using (NaturalRun.step branch (.step t712 (.step t713 (.done _)))),
      by simpa [he] using rest⟩

end DirectedFlowCutGap.GraphDiscoveryProgram
