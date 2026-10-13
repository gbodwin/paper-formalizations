import DirectedFlowCutGap.KeptAdjacencyMatrixCall

namespace DirectedFlowCutGap.KeptAdjacencyMatrix
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def matrix (kept : Bits) : List Bits → Bits → List Bits
  | u::us,z::zs => KeptAdjacencyRow.row z u kept::matrix kept us zs
  | _,_ => []
def steps (kept : Bits) : List Bits → Bits → ℕ
  | u::us,z::zs => KeptAdjacencyRow.steps z u kept+25+steps kept us zs
  | _,_ => 3
def cells (kept : Bits) : List Bits → Bits → ℕ
  | u::us,_z::zs => 5*u.length+6+cells kept us zs
  | _,_ => 1

theorem matrix_return {heap : NaturalHeap} {a b : ℕ} {kept : Bits} {vs : List Bits} {zs : Bits}
    (hv : Matrix heap a vs) (hc : Context heap b zs kept) (aligned : vs.length=zs.length) (widths : ∀ u∈vs,u.length=kept.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 84)
    (stack : List (Frame ℕ 84)) (source : Bits) :
    ∃ ext root,ext.length=cells kept vs zs ∧ NaturalRun program (steps kept vs zs)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 40) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Matrix (heap++ext) root (matrix kept vs zs) := by
  induction vs generalizing zs heap a b next c d saved pc stack with
  | nil =>
    cases zs with
    | cons z zs => simp at aligned
    | nil =>
      cases hv with
      | nil hp =>
        refine ⟨[.nil],next,rfl,?_,.nil (by simp [hn])⟩
        have a0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 40)=
            some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 41,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hp,tagBranch]
        have a1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 41)=
            some ⟨state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 42,[],0⟩ := by
          simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
        have a2 : tickNatural program (state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 42)=
            some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        exact .step a0 (.step a1 (.step a2 (.done _)))
  | cons u us ih =>
    cases zs with
    | nil => simp at aligned
    | cons z zs =>
      cases hv with
      | @cons _ up tail _ _ hp hu htail =>
        obtain ⟨flags,full,hb,hflags,hall⟩ := hc
        cases hflags with
        | @cons _ zp ztail _ _ hf hz hzt =>
          let scratch : Cell ℕ := .pair a b
          let childctx : Cell ℕ := .pair zp full
          let h0 := heap++[scratch,childctx]
          have hsc : h0[next]?=some scratch := by simp [h0,hn]
          have hcc : h0[next+1]?=some childctx := by simp [h0,hn]
          have hctx : KeptAdjacencyRow.Context h0 (next+1) z kept :=
            ⟨zp,full,hcc,lookup_extend hz _,boolList_extend hall _⟩
          have hn0 : next+2=h0.length := by simp [h0,hn]
          obtain ⟨e1,flag,l1,child,hflag⟩ := row_return (boolList_extend hu [scratch,childctx]) hctx (widths u (by simp))
            (next+2) next full hn0 ⟨up,next+1,next,full⟩ 51 (⟨pc,.r3,saved⟩::stack) source
          let saveflag : Cell ℕ := .pair next flag
          let tailctx : Cell ℕ := .pair ztail full
          let h1 := h0++e1
          let n1 := next+2+e1.length
          let h2 := h1++[saveflag,tailctx]
          have hn1 : n1=h1.length := by simp [h1,h0,n1,hn];omega
          have hsave : h2[n1]?=some saveflag := by simp [h2,hn1]
          have htailctx : h2[n1+1]?=some tailctx := by simp [h2,hn1]
          have hc2 : Context h2 (n1+1) zs kept :=
            ⟨ztail,full,htailctx,boolList_extend (boolList_extend (boolList_extend hzt _) _) _,
              boolList_extend (boolList_extend (boolList_extend hall _) _) _⟩
          have hv2 : Matrix h2 tail us := GraphDiscoveryProgram.vertices_extend
            (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend htail _) _) _
          have hn2 : n1+2=h2.length := by simp [h2,hn1]
          obtain ⟨e2,out,l2,recur,repr⟩ := ih hv2 hc2 (by simpa using aligned) (fun u hu => widths u (by simp [hu])) (n1+2) n1 ztail hn2
            ⟨tail,n1+1,n1,ztail⟩ 62 (⟨pc,.r3,saved⟩::stack)
          let output : Cell ℕ := .pair flag out
          let h3 := h2++e2
          let n3 := n1+2+e2.length
          have hf3 : BoolList (h3++[output]) flag (KeptAdjacencyRow.row z u kept) :=
            boolList_extend (boolList_extend (boolList_extend hflag _) _) _
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
            have hb1 : (h1++[saveflag])[b]?=some (.pair flags full) := lookup_extend (lookup_extend (lookup_extend hb _) _) _
            have hf1 : (h1++[saveflag])[flags]?=some (.pair zp ztail) := lookup_extend (lookup_extend (lookup_extend hf _) _) _
            have hsc1 : (h1++[saveflag])[next]?=some scratch := lookup_extend (lookup_extend hsc _) _
            have hsave1 : (h1++[saveflag])[n1]?=some saveflag := by simp [hn1]
            have t100 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 40)=
                some ⟨(state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 43),[],0⟩ := by simp [tickNatural,program,state,Registers.get,tagBranch,hp]
            have t103 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 43)=
                some ⟨(state (heap++[scratch]) (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 44),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,scratch]
            have t104 : tickNatural program (state (heap++[scratch]) (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 44)=
                some ⟨(state (heap++[scratch]) (next+1) up b next d (⟨pc,.r3,saved⟩::stack) source 45),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hp0]
            have t105 : tickNatural program (state (heap++[scratch]) (next+1) up b next d (⟨pc,.r3,saved⟩::stack) source 45)=
                some ⟨(state (heap++[scratch]) (next+1) up flags next d (⟨pc,.r3,saved⟩::stack) source 46),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
            have t106 : tickNatural program (state (heap++[scratch]) (next+1) up flags next d (⟨pc,.r3,saved⟩::stack) source 46)=
                some ⟨(state (heap++[scratch]) (next+1) up zp next d (⟨pc,.r3,saved⟩::stack) source 47),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hf0]
            have t107 : tickNatural program (state (heap++[scratch]) (next+1) up zp next d (⟨pc,.r3,saved⟩::stack) source 47)=
                some ⟨(state (heap++[scratch]) (next+1) up zp next b (⟨pc,.r3,saved⟩::stack) source 48),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hs0,scratch]
            have t108 : tickNatural program (state (heap++[scratch]) (next+1) up zp next b (⟨pc,.r3,saved⟩::stack) source 48)=
                some ⟨(state (heap++[scratch]) (next+1) up zp next full (⟨pc,.r3,saved⟩::stack) source 49),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
            have t109 : tickNatural program (state (heap++[scratch]) (next+1) up zp next full (⟨pc,.r3,saved⟩::stack) source 49)=
                some ⟨(state h0 (next+2) up (next+1) next full (⟨pc,.r3,saved⟩::stack) source 50),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,childctx,List.append_assoc,Nat.add_assoc]
            have t110 : tickNatural program (state h0 (next+2) up (next+1) next full (⟨pc,.r3,saved⟩::stack) source 50)=
                some ⟨(state h0 (next+2) up (next+1) next full (⟨51,.r3,⟨up,next+1,next,full⟩⟩::⟨pc,.r3,saved⟩::stack) source 34),[],0⟩ := by rfl
            have t111 : tickNatural program (state h1 n1 up (next+1) next flag (⟨pc,.r3,saved⟩::stack) source 51)=
                some ⟨(state (h1++[saveflag]) (n1+1) up (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 52),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,saveflag]
            have t112 : tickNatural program (state (h1++[saveflag]) (n1+1) up (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 52)=
                some ⟨(state (h1++[saveflag]) (n1+1) next (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 53),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsave1,saveflag]
            have t113 : tickNatural program (state (h1++[saveflag]) (n1+1) next (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 53)=
                some ⟨(state (h1++[saveflag]) (n1+1) a (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 54),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsc1,scratch]
            have t114 : tickNatural program (state (h1++[saveflag]) (n1+1) a (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 54)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 55),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
            have t115 : tickNatural program (state (h1++[saveflag]) (n1+1) tail (next+1) n1 flag (⟨pc,.r3,saved⟩::stack) source 55)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail next n1 flag (⟨pc,.r3,saved⟩::stack) source 56),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsave1,saveflag]
            have t116 : tickNatural program (state (h1++[saveflag]) (n1+1) tail next n1 flag (⟨pc,.r3,saved⟩::stack) source 56)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail b n1 flag (⟨pc,.r3,saved⟩::stack) source 57),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsc1,scratch]
            have t117 : tickNatural program (state (h1++[saveflag]) (n1+1) tail b n1 flag (⟨pc,.r3,saved⟩::stack) source 57)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail b n1 flags (⟨pc,.r3,saved⟩::stack) source 58),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
            have t118 : tickNatural program (state (h1++[saveflag]) (n1+1) tail b n1 flags (⟨pc,.r3,saved⟩::stack) source 58)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail b n1 ztail (⟨pc,.r3,saved⟩::stack) source 59),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hf1]
            have t119 : tickNatural program (state (h1++[saveflag]) (n1+1) tail b n1 ztail (⟨pc,.r3,saved⟩::stack) source 59)=
                some ⟨(state (h1++[saveflag]) (n1+1) tail full n1 ztail (⟨pc,.r3,saved⟩::stack) source 60),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
            have t120 : tickNatural program (state (h1++[saveflag]) (n1+1) tail full n1 ztail (⟨pc,.r3,saved⟩::stack) source 60)=
                some ⟨(state h2 (n1+2) tail (n1+1) n1 ztail (⟨pc,.r3,saved⟩::stack) source 61),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,tailctx,List.append_assoc,Nat.add_assoc]
            have t121 : tickNatural program (state h2 (n1+2) tail (n1+1) n1 ztail (⟨pc,.r3,saved⟩::stack) source 61)=
                some ⟨(state h2 (n1+2) tail (n1+1) n1 ztail (⟨62,.r3,⟨tail,n1+1,n1,ztail⟩⟩::⟨pc,.r3,saved⟩::stack) source 40),[],0⟩ := by rfl
            have t122 : tickNatural program (state h3 n3 tail (n1+1) n1 out (⟨pc,.r3,saved⟩::stack) source 62)=
                some ⟨(state h3 n3 tail (n1+1) flag out (⟨pc,.r3,saved⟩::stack) source 63),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,h3,lookup_extend hsave e2,saveflag]
            have t123 : tickNatural program (state h3 n3 tail (n1+1) flag out (⟨pc,.r3,saved⟩::stack) source 63)=
                some ⟨(state (h3++[output]) (n3+1) tail (n1+1) flag n3 (⟨pc,.r3,saved⟩::stack) source 64),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,output]
            have t124 : tickNatural program (state (h3++[output]) (n3+1) tail (n1+1) flag n3 (⟨pc,.r3,saved⟩::stack) source 64)=
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
          · have tailRep := GraphDiscoveryProgram.vertices_extend repr [output]
            simpa [matrix,h3,h2,h1,h0,List.append_assoc] using GraphDiscoveryProgram.Vertices.cons ho hf3 tailRep
end DirectedFlowCutGap.KeptAdjacencyMatrix
