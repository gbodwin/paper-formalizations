import DirectedFlowCutGap.SupportRecoveryCalls

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem flag_return (bit : Bool) (heap : NaturalHeap) (next a b c d : ℕ)
    (saved : Registers ℕ) (pc : Fin 280) (stack : List (Frame ℕ 280)) (source : Bits) :
    NaturalRun program 2
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (if bit then 112 else 114)) []
      (state (heap++[.flag bit]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have first : tickNatural program
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (if bit then 112 else 114))=
      some ⟨state (heap++[.flag bit]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack)
        source (if bit then 113 else 115),[],0⟩ := by
    cases bit <;> simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
  have last : tickNatural program
      (state (heap++[.flag bit]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack)
        source (if bit then 113 else 115))=
      some ⟨state (heap++[.flag bit]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    cases bit <;> simp [tickNatural,program,state,Registers.get,Registers.set]
  exact .step first (.step last (.done _))

theorem second_flag_return {heap : NaturalHeap} {u v : Bits} {d : ℕ}
    (tag : heap[d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u v)))
    (next a b c : ℕ) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    NaturalRun program 3
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 110) []
      (state (heap++[.flag (same u v)]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have branch : tickNatural program
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 110)=
      some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack)
        source (if same u v then 112 else 114),[],0⟩ := by
    cases ho : BinaryComparisonProgram.order u v <;>
      simp [tickNatural,program,state,Registers.get,tag,ho,BinaryComparisonProgram.tag,tagBranch,same]
  exact .step branch (flag_return (same u v) heap next a b c d saved pc stack source)

def edgeTailSteps (e f : Bits × Bits) : ℕ :=
  if same e.1 f.1 then BinaryComparisonProgram.steps e.2 f.2+11 else 3
def edgeTailCells (e f : Bits × Bits) : ℕ :=
  if same e.1 f.1 then BinaryComparisonProgram.cells e.2 f.2+1 else 1

theorem edge_tail {heap : NaturalHeap} {left right p d : ℕ} {e f : Bits × Bits}
    (he : Edge heap left e) (hf : Edge heap right f) (scratch : heap[p]?=some (.pair left right))
    (tag : heap[d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order e.1 f.1)))
    (next a b : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=edgeTailCells e f ∧
      NaturalRun program (edgeTailSteps e f)
        (state heap next a b p d (⟨pc,.r3,saved⟩::stack) source 104) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (edgeEq e f)) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  have branch : tickNatural program (state heap next a b p d frames source 104)=
      some ⟨state heap next a b p d frames source (if same e.1 f.1 then 105 else 114),[],0⟩ := by
    cases ho : BinaryComparisonProgram.order e.1 f.1 <;>
      simp [tickNatural,program,state,Registers.get,tag,ho,BinaryComparisonProgram.tag,tagBranch,same]
  by_cases hs : same e.1 f.1=true
  · obtain ⟨eu,ev,hep,_,hev⟩ := he
    obtain ⟨fu,fv,hfp,_,hfv⟩ := hf
    obtain ⟨ext,root,len,cmp,out⟩ := compare_return hev hfv next p d hn
      ⟨ev,fv,p,d⟩ 110 frames source
    have t105 : tickNatural program (state heap next a b p d frames source 105)=
        some ⟨state heap next left b p d frames source 106,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t106 : tickNatural program (state heap next left b p d frames source 106)=
        some ⟨state heap next ev b p d frames source 107,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hep]
    have t107 : tickNatural program (state heap next ev b p d frames source 107)=
        some ⟨state heap next ev right p d frames source 108,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t108 : tickNatural program (state heap next ev right p d frames source 108)=
        some ⟨state heap next ev fv p d frames source 109,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hfp]
    have t109 : tickNatural program (state heap next ev fv p d frames source 109)=
        some ⟨state heap next ev fv p d (⟨110,.r3,⟨ev,fv,p,d⟩⟩::frames) source 84,[],0⟩ := by
      simp [tickNatural,program,state]
    have finish := second_flag_return out (next+ext.length) ev fv p saved pc stack source
    simp only [hs,ite_true] at branch
    refine ⟨ext++[.flag (same e.2 f.2)],next+ext.length,by simp [edgeTailCells,hs,len],?_,?_⟩
    · convert NaturalRun.step branch (.step t105 (.step t106 (.step t107 (.step t108
        (.step t109 (run_append cmp finish)))))) using 1 <;>
        simp [edgeTailSteps,hs,List.append_assoc,state]
      omega
    · simp [edgeEq,hs,hn]
  · simp only [hs] at branch
    refine ⟨[.flag false],next,by simp [edgeTailCells,hs],?_,?_⟩
    · simpa [edgeTailSteps,hs] using NaturalRun.step branch
        (flag_return false heap next a b p d saved pc stack source)
    · simp [edgeEq,hs,hn]

theorem edge_return {heap : NaturalHeap} {a b : ℕ} {e f : Bits × Bits}
    (he : Edge heap a e) (hf : Edge heap b f) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 280) (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=edgeCells e f ∧ NaturalRun program (edgeSteps e f)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 100) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (edgeEq e f)) := by
  obtain ⟨eu,ev,hep,heu,hev⟩ := he
  obtain ⟨fu,fv,hfp,hfu,hfv⟩ := hf
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair a b]
  have dense : next+1=(heap++e0).length := by simp [e0,hn]
  obtain ⟨e1,tag,len1,cmp,htag⟩ := compare_return (boolList_extend heu e0) (boolList_extend hfu e0)
    (next+1) next d dense ⟨eu,fu,next,d⟩ 104 frames source
  obtain ⟨e2,root,len2,tail,out⟩ := edge_tail
    (edge_extend (show Edge heap a e from ⟨eu,ev,hep,heu,hev⟩) (e0++e1))
    (edge_extend (show Edge heap b f from ⟨fu,fv,hfp,hfu,hfv⟩) (e0++e1))
    (show (heap++(e0++e1))[next]?=some (.pair a b) from by simp [e0,hn])
    (by simpa [List.append_assoc] using htag)
    (next+1+e1.length) eu fu (by simp [e0,hn];omega) saved pc stack source
  have t100 : tickNatural program (state heap next a b c d frames source 100)=
      some ⟨state (heap++e0) (next+1) a b next d frames source 101,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e0]
  have t101 : tickNatural program (state (heap++e0) (next+1) a b next d frames source 101)=
      some ⟨state (heap++e0) (next+1) eu b next d frames source 102,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hep e0]
  have t102 : tickNatural program (state (heap++e0) (next+1) eu b next d frames source 102)=
      some ⟨state (heap++e0) (next+1) eu fu next d frames source 103,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hfp e0]
  have t103 : tickNatural program (state (heap++e0) (next+1) eu fu next d frames source 103)=
      some ⟨state (heap++e0) (next+1) eu fu next d
        (⟨104,.r3,⟨eu,fu,next,d⟩⟩::frames) source 84,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨e0++e1++e2,root,?_,?_,?_⟩
  · simp [edgeCells,edgeTailCells,e0,len1,len2];split <;> omega
  · have joined := NaturalRun.step t100 (.step t101 (.step t102 (.step t103
        (run_append cmp (by simpa [List.append_assoc] using tail)))))
    convert joined using 1 <;> simp [edgeSteps,edgeTailSteps,e0,state]
    all_goals first | omega | (split <;> omega)
  · simpa [List.append_assoc] using out

end DirectedFlowCutGap.SupportRecoveryProgram
