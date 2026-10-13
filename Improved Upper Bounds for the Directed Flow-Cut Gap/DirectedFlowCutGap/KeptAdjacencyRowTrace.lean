import DirectedFlowCutGap.KeptAdjacencyRowFlag

namespace DirectedFlowCutGap.KeptAdjacencyRow
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem row_return {heap : NaturalHeap} {a b : ℕ} {adj kept : Bits} {keep : Bool}
    (ha : BoolList heap a adj) (hc : Context heap b keep kept) (aligned : adj.length=kept.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 36)
    (stack : List (Frame ℕ 36)) (source : Bits) :
    ∃ ext root,ext.length=5*adj.length+1 ∧ NaturalRun program (steps keep adj kept)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (row keep adj kept) := by
  induction adj generalizing kept heap a b next c d saved pc stack with
  | nil =>
    cases kept with
    | cons k ks => simp at aligned
    | nil =>
      cases ha with
      | nil hp =>
        refine ⟨[.nil],next,rfl,?_,.nil (by simp [hn])⟩
        have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
            some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hp,tagBranch]
        have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1)=
            some ⟨state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 2,[],0⟩ := by
          simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
        have t2 : tickNatural program (state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 2)=
            some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        exact .step t0 (.step t1 (.step t2 (.done _)))
  | cons av adj ih =>
    cases kept with
    | nil => simp at aligned
    | cons kv kept =>
      cases ha with
      | @cons _ ap atail _ _ hp hav hat =>
        obtain ⟨kp,ks,hb,hku,hks⟩ := hc
        cases hks with
        | @cons _ vp vt _ _ hks hvv hkt =>
          let scratch : Cell ℕ := .pair a b
          let result : Cell ℕ := .flag (av && keep && kv)
          let h0 := heap++[scratch,result]
          have hsc : h0[next]?=some scratch := by simp [h0,hn]
          have hres : h0[next+1]?=some result := by simp [h0,hn]
          have first := flag_trace hp hav hb hku hks hvv next c d hn (⟨pc,.r3,saved⟩::stack) source
          let n0 := next+2
          let savedResult : Cell ℕ := .pair next (next+1)
          let tailctx : Cell ℕ := .pair kp vt
          let h1 := h0++[savedResult,tailctx]
          have hn0 : n0=h0.length := by simp [n0,h0,hn]
          have hsave : h1[n0]?=some savedResult := by simp [h1,hn0]
          have hctx : h1[n0+1]?=some tailctx := by simp [h1,hn0]
          have hc1 : Context h1 (n0+1) keep kept :=
            ⟨kp,vt,hctx,lookup_extend (lookup_extend hku _) _,boolList_extend (boolList_extend hkt _) _⟩
          have ha1 := boolList_extend (boolList_extend hat [scratch,result]) [savedResult,tailctx]
          have hn1 : n0+2=h1.length := by simp [h1,hn0]
          obtain ⟨ext,out,len,recur,rep⟩ := ih ha1 hc1 (by simpa using aligned) (n0+2) n0 vt hn1
            ⟨atail,n0+1,n0,vt⟩ 28 (⟨pc,.r3,saved⟩::stack)
          let output : Cell ℕ := .pair (next+1) out
          let h2 := h1++ext
          let n2 := n0+2+ext.length
          have hout : (h2++[output])[n2]?=some output := by
            have hlen : n2=h2.length := by simp [h2,n2,hn1]
            simp [hlen]
          have hflag : (h2++[output])[next+1]?=some result :=
            lookup_extend (lookup_extend (lookup_extend hres _) _) _
          refine ⟨[scratch,result]++[savedResult,tailctx]++ext++[output],n2,?_,?_,?_⟩
          · simp [len];omega
          · have hs0 : (h0++[savedResult])[next]?=some scratch := lookup_extend hsc _
            have hr0 : (h0++[savedResult])[n0]?=some savedResult := by simp [hn0]
            have hp0 : (h0++[savedResult])[a]?=some (.pair ap atail) := lookup_extend (lookup_extend hp _) _
            have hb0 : (h0++[savedResult])[b]?=some (.pair kp ks) := lookup_extend (lookup_extend hb _) _
            have hk0 : (h0++[savedResult])[ks]?=some (.pair vp vt) := lookup_extend (lookup_extend hks _) _
            have t17 : tickNatural program (state h0 n0 a b next (next+1) (⟨pc,.r3,saved⟩::stack) source 17)=
                some ⟨(state (h0++[savedResult]) (n0+1) a b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 18),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,savedResult]
            have t18 : tickNatural program (state (h0++[savedResult]) (n0+1) a b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 18)=
                some ⟨(state (h0++[savedResult]) (n0+1) next b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 19),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hr0,savedResult]
            have t19 : tickNatural program (state (h0++[savedResult]) (n0+1) next b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 19)=
                some ⟨(state (h0++[savedResult]) (n0+1) a b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 20),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hs0,scratch]
            have t20 : tickNatural program (state (h0++[savedResult]) (n0+1) a b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 20)=
                some ⟨(state (h0++[savedResult]) (n0+1) atail b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 21),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hp0]
            have t21 : tickNatural program (state (h0++[savedResult]) (n0+1) atail b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 21)=
                some ⟨(state (h0++[savedResult]) (n0+1) atail next n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 22),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hr0,savedResult]
            have t22 : tickNatural program (state (h0++[savedResult]) (n0+1) atail next n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 22)=
                some ⟨(state (h0++[savedResult]) (n0+1) atail b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 23),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hs0,scratch]
            have t23 : tickNatural program (state (h0++[savedResult]) (n0+1) atail b n0 (next+1) (⟨pc,.r3,saved⟩::stack) source 23)=
                some ⟨(state (h0++[savedResult]) (n0+1) atail b n0 ks (⟨pc,.r3,saved⟩::stack) source 24),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
            have t24 : tickNatural program (state (h0++[savedResult]) (n0+1) atail b n0 ks (⟨pc,.r3,saved⟩::stack) source 24)=
                some ⟨(state (h0++[savedResult]) (n0+1) atail b n0 vt (⟨pc,.r3,saved⟩::stack) source 25),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hk0]
            have t25 : tickNatural program (state (h0++[savedResult]) (n0+1) atail b n0 vt (⟨pc,.r3,saved⟩::stack) source 25)=
                some ⟨(state (h0++[savedResult]) (n0+1) atail kp n0 vt (⟨pc,.r3,saved⟩::stack) source 26),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
            have t26 : tickNatural program (state (h0++[savedResult]) (n0+1) atail kp n0 vt (⟨pc,.r3,saved⟩::stack) source 26)=
                some ⟨(state h1 (n0+2) atail (n0+1) n0 vt (⟨pc,.r3,saved⟩::stack) source 27),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1,tailctx,List.append_assoc,Nat.add_assoc]
            have t27 : tickNatural program (state h1 (n0+2) atail (n0+1) n0 vt (⟨pc,.r3,saved⟩::stack) source 27)=
                some ⟨(state h1 (n0+2) atail (n0+1) n0 vt (⟨28,.r3,⟨atail,n0+1,n0,vt⟩⟩::⟨pc,.r3,saved⟩::stack) source 0),[],0⟩ := by rfl
            have t28 : tickNatural program (state h2 n2 atail (n0+1) n0 out (⟨pc,.r3,saved⟩::stack) source 28)=
                some ⟨(state h2 n2 atail (n0+1) (next+1) out (⟨pc,.r3,saved⟩::stack) source 29),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,h2,lookup_extend hsave ext,savedResult]
            have t29 : tickNatural program (state h2 n2 atail (n0+1) (next+1) out (⟨pc,.r3,saved⟩::stack) source 29)=
                some ⟨(state (h2++[output]) (n2+1) atail (n0+1) (next+1) n2 (⟨pc,.r3,saved⟩::stack) source 30),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,output]
            have t30 : tickNatural program (state (h2++[output]) (n2+1) atail (n0+1) (next+1) n2 (⟨pc,.r3,saved⟩::stack) source 30)=
                some ⟨(state (h2++[output]) (n2+1) saved.a saved.b saved.c n2 stack source pc),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set]
            have last := run_append recur (.step t28 (.step t29 (.step t30 (.done _))))
            have rest := NaturalRun.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22
              (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 last))))))))))
            have whole := run_append first rest
            have count : (if av then if keep then 24 else 21 else 19)=flagSteps av keep+14 := by
              cases av <;> cases keep <;> rfl
            convert whole using 1 <;> simp [steps,count,state,h2,h1,h0,n2,n0,scratch,result,
              List.append_assoc,Nat.add_assoc] <;> omega
          · simpa [row,h2,h1,h0,result,List.append_assoc] using BoolList.cons hout hflag (boolList_extend rep [output])
end DirectedFlowCutGap.KeptAdjacencyRow
