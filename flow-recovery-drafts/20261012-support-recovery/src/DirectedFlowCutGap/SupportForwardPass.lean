import DirectedFlowCutGap.SupportForwardTransitions
import DirectedFlowCutGap.SupportSearchInvariants

/-! Each later vertex reads the table returned by the earlier actual visit. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem pass_return {heap : NaturalHeap} {a b : ℕ} {adjacency : List Bits}
    {es : List (Bits × Bits)} {vs : List Bits} {xs : List Code} (N : ℕ)
    (input : Vertices heap a vs) (context : StoredVisitContext heap b adjacency es xs)
    (rows : N≤adjacency.length) (cols : ∀ (i : ℕ) (hi : i<N), N≤(adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (hx : ∀ x∈xs,value x.1<N)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=passCells adjacency es vs xs ∧
      NaturalRun program (passSteps adjacency es vs xs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 220) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Codes (heap++ext) root (pass adjacency es vs xs) := by
  induction vs generalizing heap a b xs next c d saved pc stack with
  | nil =>
    cases input with
    | nil hp =>
      obtain ⟨table,supp,hctx,ht,_⟩ := context
      let frames := (⟨pc,.r3,saved⟩::stack)
      have t220 : tickNatural program (state heap next a b c d frames source 220)=
          some ⟨state heap next a b c d frames source 221,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t221 : tickNatural program (state heap next a b c d frames source 221)=
          some ⟨state heap next a b c table frames source 222,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
      have t222 : tickNatural program (state heap next a b c table frames source 222)=
          some ⟨state heap next saved.a saved.b saved.c table stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      refine ⟨[],table,rfl,?_,by simpa [pass] using ht⟩
      simpa [passSteps] using (NaturalRun.step t220 (.step t221 (.step t222 (.done _))))
  | cons u us ih =>
    cases input with
    | @cons _ head tail _ _ hp hu ht =>
      obtain ⟨table,supp,hctx,hcodes,hsupp⟩ := context
      let frames := (⟨pc,.r3,saved⟩::stack)
      let e0 : NaturalHeap := [.pair a b]
      have scratch : (heap++e0)[next]?=some (.pair a b) := by simp [e0,hn]
      have huN := hv u (by simp)
      have oldctx : StoredVisitContext heap b adjacency es xs := ⟨table,supp,hctx,hcodes,hsupp⟩
      obtain ⟨e1,newtable,len1,visitRun,newcodes⟩ := visit_return (boolList_extend hu e0)
        (visitContext_extend oldctx e0) (lt_of_lt_of_le huN rows)
        (fun x hx' => lt_of_lt_of_le (hx x hx') (cols _ huN))
        (next+1) next d (by simp [e0,hn]) ⟨head,b,next,d⟩ 227 frames source
      let e2 : NaturalHeap := [.pair newtable supp]
      have dense1 : next+1+e1.length=((heap++e0)++e1).length := by simp [e0,hn];omega
      have newctx : StoredVisitContext (((heap++e0)++e1)++e2) (next+1+e1.length)
          adjacency es (visit adjacency es u xs) := by
        exact ⟨newtable,supp,by rw [dense1];simp [e2],codes_extend newcodes e2,
          supportContext_extend (supportContext_extend (supportContext_extend hsupp e0) e1) e2⟩
      obtain ⟨e3,root,len3,tailRun,out⟩ := ih
        (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend
          (GraphDiscoveryProgram.vertices_extend ht e0) e1) e2) newctx
        (fun v h => hv v (by simp [h])) (visit_valid adjacency es u xs N huN hx)
        (next+1+e1.length+1) next newtable (by simp [e0,e2,hn];omega)
        ⟨tail,next+1+e1.length,next,newtable⟩ 233 frames
      have headRun := pass_head (b:=b) hp next c d frames source
      have continueRun := pass_continue (lookup_extend scratch e1)
        (lookup_extend (lookup_extend hctx e0) e1) (lookup_extend (lookup_extend hp e0) e1)
        (next+1+e1.length) newtable frames source
      have t233 : tickNatural program
          (state ((((heap++e0)++e1)++e2)++e3) (next+1+e1.length+1+e3.length)
            tail (next+1+e1.length) next root frames source 233)=
          some ⟨state ((((heap++e0)++e1)++e2)++e3) (next+1+e1.length+1+e3.length)
            saved.a saved.b saved.c root stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      refine ⟨e0++e1++e2++e3,root,by simp [passCells,e0,e2,len1,len3];omega,?_,?_⟩
      · have joined := run_append headRun (run_append visitRun
          (run_append continueRun (run_append tailRun (.step t233 (.done _)))))
        convert joined using 1 <;> simp [passSteps,e0,e2,List.append_assoc,state]
        all_goals omega
      · simpa [pass,List.append_assoc] using out

end DirectedFlowCutGap.SupportRecoveryProgram
