import DirectedFlowCutGap.SupportVisitAllocation

/-! The actual missing-key branch calls the support predecessor scan on the
current table. Only an actual hit allocates the new retained edge and code. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def missingSteps (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) (xs : List Code) : ℕ :=
  predSteps adjacency es u xs + match predecessor adjacency es u xs with | none => 11 | some _ => 18
def missingCells (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) (xs : List Code) : ℕ :=
  1+predCells adjacency es u xs + match predecessor adjacency es u xs with | none => 0 | some _ => 4
def missingVisit (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) (xs : List Code) : List Code :=
  match predecessor adjacency es u xs with | none => xs | some x => (u,(u,x.1)::x.2)::xs

theorem missing_return {heap : NaturalHeap} {p ur ctx : ℕ} {adjacency : List Bits}
    {es : List (Bits × Bits)} {u : Bits} {xs : List Code}
    (scratch : heap[p]?=some (.pair ur ctx)) (word : BoolList heap ur u)
    (context : StoredVisitContext heap ctx adjacency es xs)
    (hi : value u<adjacency.length) (hj : ∀ x∈xs,value x.1<(adjacency[value u]).length)
    (next a b d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=missingCells adjacency es u xs ∧
      NaturalRun program (missingSteps adjacency es u xs)
        (state heap next a b p d (⟨pc,.r3,saved⟩::stack) source 195) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Codes (heap++ext) root (missingVisit adjacency es u xs) := by
  obtain ⟨table,supp,hctx,ht,hs⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair ur supp]
  have newctx : StoredPredContext (heap++e0) next adjacency es u := by
    exact ⟨ur,supp,by simp [e0,hn],boolList_extend word e0,supportContext_extend hs e0⟩
  obtain ⟨e1,pred,len1,body,out⟩ := predecessor_return (codes_extend ht e0) newctx hi hj
    (next+1) p supp (by simp [e0,hn]) ⟨table,next,p,supp⟩ 202 frames source
  have t195 : tickNatural program (state heap next a b p d frames source 195)=
      some ⟨state heap next ctx b p d frames source 196,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t196 : tickNatural program (state heap next ctx b p d frames source 196)=
      some ⟨state heap next table b p d frames source 197,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
  have t197 : tickNatural program (state heap next table b p d frames source 197)=
      some ⟨state heap next table ur p d frames source 198,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t198 : tickNatural program (state heap next table ur p d frames source 198)=
      some ⟨state heap next table ur p ctx frames source 199,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t199 : tickNatural program (state heap next table ur p ctx frames source 199)=
      some ⟨state heap next table ur p supp frames source 200,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
  have t200 : tickNatural program (state heap next table ur p supp frames source 200)=
      some ⟨state (heap++e0) (next+1) table next p supp frames source 201,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,e0]
  have t201 : tickNatural program (state (heap++e0) (next+1) table next p supp frames source 201)=
      some ⟨state (heap++e0) (next+1) table next p supp
        (⟨202,.r3,⟨table,next,p,supp⟩⟩::frames) source 170,[],0⟩ := by
    simp [tickNatural,program,state]
  have preRun := NaturalRun.step t195 (.step t196 (.step t197 (.step t198
    (.step t199 (.step t200 (.step t201 body))))))
  have oldctx : StoredVisitContext ((heap++e0)++e1) ctx adjacency es xs :=
    visitContext_extend (visitContext_extend ⟨table,supp,hctx,ht,hs⟩ e0) e1
  have oldscratch := lookup_extend (lookup_extend scratch e0) e1
  cases pick : predecessor adjacency es u xs with
  | none =>
    have hnil : ((heap++e0)++e1)[pred]?=some .nil := by simpa [pick,StoredOption] using out
    simp only [List.append_assoc] at hnil
    have t202 : tickNatural program
        (state ((heap++e0)++e1) (next+1+e1.length) table next p pred frames source 202)=
        some ⟨state ((heap++e0)++e1) (next+1+e1.length) table next p pred frames source 215,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
    obtain ⟨root,tail,rep⟩ := keep_return oldscratch oldctx (next+1+e1.length)
      table next pred saved pc stack source
    refine ⟨e0++e1,root,by simp [missingCells,pick,e0,len1];omega,?_,?_⟩
    · convert run_append preRun (.step t202 tail) using 1 <;>
        simp [missingSteps,pick,e0,List.append_assoc,state]
      all_goals omega
    · simpa [missingVisit,pick,List.append_assoc] using rep
  | some x =>
    have hcode : StoredCode ((heap++e0)++e1) pred x := by simpa [pick,StoredOption] using out
    obtain ⟨xv,xe,hp,hxv,hxe⟩ := hcode
    have hp' := hp
    simp only [List.append_assoc] at hp'
    have t202 : tickNatural program
        (state ((heap++e0)++e1) (next+1+e1.length) table next p pred frames source 202)=
        some ⟨state ((heap++e0)++e1) (next+1+e1.length) table next p pred frames source 203,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp',tagBranch]
    obtain ⟨e2,root,len2,tail,rep⟩ := prepend_return oldscratch
      (boolList_extend (boolList_extend word e0) e1) oldctx (x:=x) ⟨xv,xe,hp,hxv,hxe⟩ (next+1+e1.length)
      table next (by simp [e0,hn];omega) saved pc stack source
    refine ⟨e0++e1++e2,root,by simp [missingCells,pick,e0,len1,len2];omega,?_,?_⟩
    · convert run_append preRun (.step t202 tail) using 1 <;>
        simp [missingSteps,pick,e0,len2,List.append_assoc,state]
      all_goals omega
    · simpa [missingVisit,pick,List.append_assoc] using rep

end DirectedFlowCutGap.SupportRecoveryProgram
