import DirectedFlowCutGap.SupportVisitDecision

/-! Literal forward-updating visit of a single represented vertex. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem visit_return {heap : NaturalHeap} {a b : ℕ} {adjacency : List Bits}
    {es : List (Bits × Bits)} {u : Bits} {xs : List Code}
    (word : BoolList heap a u) (context : StoredVisitContext heap b adjacency es xs)
    (hi : value u<adjacency.length) (hj : ∀ x∈xs,value x.1<(adjacency[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=visitCells adjacency es u xs ∧
      NaturalRun program (visitSteps adjacency es u xs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 190) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Codes (heap++ext) root (visit adjacency es u xs) := by
  obtain ⟨table,supp,hctx,ht,hs⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair a b]
  have scratch : (heap++e0)[next]?=some (.pair a b) := by simp [e0,hn]
  obtain ⟨e1,found,len1,body,out⟩ := lookup_return (codes_extend ht e0) (boolList_extend word e0)
    (next+1) next d (by simp [e0,hn]) ⟨table,a,next,d⟩ 194 frames source
  have t190 : tickNatural program (state heap next a b c d frames source 190)=
      some ⟨state (heap++e0) (next+1) a b next d frames source 191,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,e0]
  have t191 : tickNatural program (state (heap++e0) (next+1) a b next d frames source 191)=
      some ⟨state (heap++e0) (next+1) table b next d frames source 192,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hctx e0]
  have t192 : tickNatural program (state (heap++e0) (next+1) table b next d frames source 192)=
      some ⟨state (heap++e0) (next+1) table a next d frames source 193,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t193 : tickNatural program (state (heap++e0) (next+1) table a next d frames source 193)=
      some ⟨state (heap++e0) (next+1) table a next d
        (⟨194,.r3,⟨table,a,next,d⟩⟩::frames) source 150,[],0⟩ := by
    simp [tickNatural,program,state]
  have preRun := NaturalRun.step t190 (.step t191 (.step t192 (.step t193 body)))
  have oldctx : StoredVisitContext ((heap++e0)++e1) b adjacency es xs :=
    visitContext_extend (visitContext_extend ⟨table,supp,hctx,ht,hs⟩ e0) e1
  have oldscratch := lookup_extend scratch e1
  cases pick : lookup u xs with
  | none =>
    have hnil : ((heap++e0)++e1)[found]?=some .nil := by simpa [pick,StoredOption] using out
    simp only [List.append_assoc] at hnil
    have t194 : tickNatural program
        (state ((heap++e0)++e1) (next+1+e1.length) table a next found frames source 194)=
        some ⟨state ((heap++e0)++e1) (next+1+e1.length) table a next found frames source 195,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
    obtain ⟨e2,root,len2,tail,rep⟩ := missing_return oldscratch
      (boolList_extend (boolList_extend word e0) e1) oldctx hi hj
      (next+1+e1.length) table a found (by simp [e0,hn];omega) saved pc stack source
    refine ⟨e0++e1++e2,root,?_,?_,?_⟩
    · cases hpick : predecessor adjacency es u xs <;>
        simp [visitCells,pick,e0,len1,len2,missingCells,hpick] <;> ring
    · convert run_append preRun (.step t194 tail) using 1 <;>
        simp [visitSteps,pick,missingSteps,e0,List.append_assoc,state]
      all_goals first | omega | (cases predecessor adjacency es u xs <;> simp only <;> ring)
    · cases hpick : predecessor adjacency es u xs <;>
        simpa [visit,pick,missingVisit,hpick,List.append_assoc] using rep
  | some x =>
    have hcode : StoredCode ((heap++e0)++e1) found x := by simpa [pick,StoredOption] using out
    obtain ⟨xv,xe,hp,_,_⟩ := hcode
    simp only [List.append_assoc] at hp
    have t194 : tickNatural program
        (state ((heap++e0)++e1) (next+1+e1.length) table a next found frames source 194)=
        some ⟨state ((heap++e0)++e1) (next+1+e1.length) table a next found frames source 215,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    obtain ⟨root,tail,rep⟩ := keep_return oldscratch oldctx (next+1+e1.length)
      table a found saved pc stack source
    refine ⟨e0++e1,root,by simp [visitCells,pick,e0,len1];omega,?_,?_⟩
    · convert run_append preRun (.step t194 tail) using 1 <;>
        simp [visitSteps,pick,e0,List.append_assoc,state]
      all_goals omega
    · simpa [visit,pick,List.append_assoc] using rep

end DirectedFlowCutGap.SupportRecoveryProgram
