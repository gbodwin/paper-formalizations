import DirectedFlowCutGap.KeptMaskCall

namespace DirectedFlowCutGap.KeptMask
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def mask (s t : Bits) : List Bits → Bits → Bits
  | u::us,z::zs => KeptVertex.bit s t u z::mask s t us zs
  | _,_ => []
def steps (s t : Bits) : List Bits → Bits → ℕ
  | u::us,z::zs => KeptVertex.keepSteps s t u z+25+steps s t us zs
  | _,_ => 3
def cells (s t : Bits) : List Bits → Bits → ℕ
  | u::us,z::zs => KeptVertex.keepCells s t u z+5+cells s t us zs
  | _,_ => 1

theorem mask_return {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits} {zs : Bits}
    (hv : Vertices heap a vs) (hc : Context heap b s t zs) (aligned : vs.length=zs.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 132)
    (stack : List (Frame ℕ 132)) (source : Bits) :
    ∃ ext root,ext.length=cells s t vs zs ∧ NaturalRun program (steps s t vs zs)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 100) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (mask s t vs zs) := by
  induction vs generalizing zs heap a b next c d saved pc stack with
  | nil =>
    cases zs with
    | cons z zs => simp at aligned
    | nil =>
      cases hv with
      | nil hp =>
        refine ⟨[.nil],next,rfl,?_,.nil (by simp [hn])⟩
        have a0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 100)=
            some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 101,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hp,tagBranch]
        have a1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 101)=
            some ⟨state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 102,[],0⟩ := by
          simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
        have a2 : tickNatural program (state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 102)=
            some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        exact .step a0 (.step a1 (.step a2 (.done _)))
  | cons u us ih =>
    cases zs with
    | nil => simp at aligned
    | cons z zs =>
      cases hv with
      | @cons _ up tail _ _ hp hu htail =>
        obtain ⟨ep,sr,tr,flags,hb,he,hs,ht,hflags⟩ := hc
        cases hflags with
        | @cons _ zp ztail _ _ hf hz hzt =>
          let scratch : Cell ℕ := .pair a b
          let childctx : Cell ℕ := .pair ep zp
          let h0 := heap++[scratch,childctx]
          have hsc : h0[next]?=some scratch := by simp [h0,hn]
          have hcc : h0[next+1]?=some childctx := by simp [h0,hn]
          have hctx : KeptVertex.Context h0 (next+1) s t z :=
            ⟨ep,sr,tr,zp,hcc,lookup_extend he _,boolList_extend hs _,boolList_extend ht _,lookup_extend hz _⟩
          have hn0 : next+2=h0.length := by simp [h0,hn]
          obtain ⟨e1,flag,l1,child,hflag⟩ := keep_return (boolList_extend hu [scratch,childctx]) hctx
            (next+2) next ep hn0 ⟨up,next+1,next,ep⟩ 111 (⟨pc,.r3,saved⟩::stack) source
          let saveflag : Cell ℕ := .pair next flag
          let tailctx : Cell ℕ := .pair ep ztail
          let h1 := h0++e1
          let n1 := next+2+e1.length
          let h2 := h1++[saveflag,tailctx]
          have hn1 : n1=h1.length := by simp [h1,h0,n1,hn];omega
          have hsave : h2[n1]?=some saveflag := by simp [h2,hn1]
          have htailctx : h2[n1+1]?=some tailctx := by simp [h2,hn1]
          have hc2 : Context h2 (n1+1) s t zs :=
            ⟨ep,sr,tr,ztail,htailctx,lookup_extend (lookup_extend (lookup_extend he _) _) _,
              boolList_extend (boolList_extend (boolList_extend hs _) _) _,
              boolList_extend (boolList_extend (boolList_extend ht _) _) _,
              boolList_extend (boolList_extend (boolList_extend hzt _) _) _⟩
          have hv2 : Vertices h2 tail us := GraphDiscoveryProgram.vertices_extend
            (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend htail _) _) _
          have hn2 : n1+2=h2.length := by simp [h2,hn1]
          obtain ⟨e2,out,l2,recur,repr⟩ := ih hv2 hc2 (by simpa using aligned) (n1+2) n1 ztail hn2
            ⟨tail,n1+1,n1,ztail⟩ 122 (⟨pc,.r3,saved⟩::stack)
          let output : Cell ℕ := .pair flag out
          let h3 := h2++e2
          let n3 := n1+2+e2.length
          have hf3 : (h3++[output])[flag]?=some (.flag (KeptVertex.bit s t u z)) :=
            lookup_extend (lookup_extend (lookup_extend hflag _) _) _
          have ho : (h3++[output])[n3]?=some output := by
            have hlen : n3=h3.length := by simp [h3,n3,hn2]
            simp [hlen]
          refine ⟨[scratch,childctx]++e1++[saveflag,tailctx]++e2++[output],n3,?_,?_,?_⟩
          · simp [cells,l1,l2];omega
          · have hp0 := lookup_extend hp [scratch]
            have hb0 := lookup_extend hb [scratch]
            have hf0 := lookup_extend hf [scratch]
            have hs0 : (heap++[scratch])[next]?=some scratch := by simp [hn]
            have hp1 : (h1++[saveflag])[a]?=some (.pair up tail) := lookup_extend (lookup_extend (lookup_extend hp _) _) _
            have hb1 : (h1++[saveflag])[b]?=some (.pair ep flags) := lookup_extend (lookup_extend (lookup_extend hb _) _) _
            have hf1 : (h1++[saveflag])[flags]?=some (.pair zp ztail) := lookup_extend (lookup_extend (lookup_extend hf _) _) _
            have hsc1 : (h1++[saveflag])[next]?=some scratch := lookup_extend (lookup_extend hsc _) _
            have hsave1 : (h1++[saveflag])[n1]?=some saveflag := by simp [hn1]
            have t100 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 100)=
                some ⟨(state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 103),[],0⟩ := by simp [tickNatural,program,state,Registers.get,tagBranch,hp]
            have t103 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 103)=
                some ⟨(state (heap++[scratch]) (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 104),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,scratch]
            have t104 : tickNatural program (state (heap++[scratch]) (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 104)=
                some ⟨(state (heap++[scratch]) (next+1) up b next d (⟨pc,.r3,saved⟩::stack) source 105),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hp0]
            have t105 : tickNatural program (state (heap++[scratch]) (next+1) up b next d (⟨pc,.r3,saved⟩::stack) source 105)=
                some ⟨(state (heap++[scratch]) (next+1) up flags next d (⟨pc,.r3,saved⟩::stack) source 106),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
            have t106 : tickNatural program (state (heap++[scratch]) (next+1) up flags next d (⟨pc,.r3,saved⟩::stack) source 106)=
                some ⟨(state (heap++[scratch]) (next+1) up zp next d (⟨pc,.r3,saved⟩::stack) source 107),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hf0]
            have t107 : tickNatural program (state (heap++[scratch]) (next+1) up zp next d (⟨pc,.r3,saved⟩::stack) source 107)=
                some ⟨(state (heap++[scratch]) (next+1) up zp next b (⟨pc,.r3,saved⟩::stack) source 108),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hs0,scratch]
            have t108 : tickNatural program (state (heap++[scratch]) (next+1) up zp next b (⟨pc,.r3,saved⟩::stack) source 108)=
                some ⟨(state (heap++[scratch]) (next+1) up zp next ep (⟨pc,.r3,saved⟩::stack) source 109),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
            have t109 : tickNatural program (state (heap++[scratch]) (next+1) up zp next ep (⟨pc,.r3,saved⟩::stack) source 109)=
                some ⟨(state h0 (next+2) up (next+1) next ep (⟨pc,.r3,saved⟩::stack) source 110),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,childctx,List.append_assoc,Nat.add_assoc]
            have t110 : tickNatural program (state h0 (next+2) up (next+1) next ep (⟨pc,.r3,saved⟩::stack) source 110)=
                some ⟨(state h0 (next+2) up (next+1) next ep (⟨111,.r3,⟨up,next+1,next,ep⟩⟩::⟨pc,.r3,saved⟩::stack) source 78),[],0⟩ := by rfl
            have t111 : tickNatural program (state h1 n1 up (next+1) next flag (⟨pc,.r3,saved⟩::stack) source 111)=
                some ⟨(state (h1++[saveflag]) (n1+1) up (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 112),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,saveflag]
            have t112 : tickNatural program (state (h1++[saveflag]) (n1+1) up (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 112)=
                some ⟨(state (h1++[saveflag]) (n1+1) next (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 113),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsave1,saveflag]
            have t113 : tickNatural program (state (h1++[saveflag]) (n1+1) next (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 113)=
                some ⟨(state (h1++[saveflag]) (n1+1) a (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 114),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsc1,scratch]
            have t114 : tickNatural program (state (h1++[saveflag]) (n1+1) a (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 114)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 115),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
            have t115 : tickNatural program (state (h1++[saveflag]) (n1+1) tail (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 115)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail next n1 flag (⟨pc,.r3,saved⟩::stack) source 116),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsave1,saveflag]
            have t116 : tickNatural program (state (h1++[saveflag]) (n1+1) tail next n1 flag (⟨pc,.r3,saved⟩::stack) source 116)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail b n1 flag (⟨pc,.r3,saved⟩::stack) source 117),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsc1,scratch]
            have t117 : tickNatural program (state (h1++[saveflag]) (n1+1) tail b n1 flag (⟨pc,.r3,saved⟩::stack) source 117)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail b n1 flags (⟨pc,.r3,saved⟩::stack) source 118),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
            have t118 : tickNatural program (state (h1++[saveflag]) (n1+1) tail b n1 flags (⟨pc,.r3,saved⟩::stack) source 118)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail b n1 ztail (⟨pc,.r3,saved⟩::stack) source 119),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hf1]
            have t119 : tickNatural program (state (h1++[saveflag]) (n1+1) tail b n1 ztail (⟨pc,.r3,saved⟩::stack) source 119)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail ep n1 ztail (⟨pc,.r3,saved⟩::stack) source 120),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
            have t120 : tickNatural program (state (h1++[saveflag]) (n1+1) tail ep n1 ztail (⟨pc,.r3,saved⟩::stack) source 120)=
                some ⟨(state h2 (n1+2) tail (n1+1) n1 ztail (⟨pc,.r3,saved⟩::stack) source 121),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,tailctx,List.append_assoc,Nat.add_assoc]
            have t121 : tickNatural program (state h2 (n1+2) tail (n1+1) n1 ztail (⟨pc,.r3,saved⟩::stack) source 121)=
                some ⟨(state h2 (n1+2) tail (n1+1) n1 ztail (⟨122,.r3,⟨tail,n1+1,n1,ztail⟩⟩::⟨pc,.r3,saved⟩::stack) source 100),[],0⟩ := by rfl
            have t122 : tickNatural program (state h3 n3 tail (n1+1) n1 out (⟨pc,.r3,saved⟩::stack) source 122)=
                some ⟨(state h3 n3 tail (n1+1) flag out (⟨pc,.r3,saved⟩::stack) source 123),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,h3,lookup_extend hsave e2,saveflag]
            have t123 : tickNatural program (state h3 n3 tail (n1+1) flag out (⟨pc,.r3,saved⟩::stack) source 123)=
                some ⟨(state (h3++[output]) (n3+1) tail (n1+1) flag n3 (⟨pc,.r3,saved⟩::stack) source 124),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,output]
            have t124 : tickNatural program (state (h3++[output]) (n3+1) tail (n1+1) flag n3 (⟨pc,.r3,saved⟩::stack) source 124)=
                some ⟨(state (h3++[output]) (n3+1) saved.a saved.b saved.c n3 stack source pc),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set]
            have last := NaturalRun.step t122 (.step t123 (.step t124 (.done _)))
            have afterRecur := run_append recur last
            have afterChild := NaturalRun.step t111 (.step t112 (.step t113 (.step t114 (.step t115
              (.step t116 (.step t117 (.step t118 (.step t119 (.step t120 (.step t121 afterRecur))))))))))
            have withChild := run_append child afterChild
            have whole := NaturalRun.step t100 (.step t103 (.step t104 (.step t105 (.step t106
              (.step t107 (.step t108 (.step t109 (.step t110 withChild))))))))
            convert whole using 1 <;>
              simp [steps,state,h3,h2,h1,h0,n3,n1,List.append_assoc,Nat.add_assoc] <;> omega
          · have tailRep := boolList_extend repr [output]
            simpa [mask,h3,h2,h1,h0,List.append_assoc] using BoolList.cons ho hf3 tailRep
end DirectedFlowCutGap.KeptMask
