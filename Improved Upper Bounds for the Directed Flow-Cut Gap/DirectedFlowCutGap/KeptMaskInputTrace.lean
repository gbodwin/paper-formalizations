import DirectedFlowCutGap.KeptMaskInputCalls

namespace DirectedFlowCutGap.KeptMaskInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def mask (s t : Bits) (vs : List Bits) (rows : List (Bits × Bits)) : Bits :=
  KeptMask.mask s t vs (PackingZeroMask.mask rows)
def steps (s t : Bits) (vs : List Bits) (rows : List (Bits × Bits)) : ℕ :=
  PackingZeroMask.steps rows+KeptMask.steps s t vs (PackingZeroMask.mask rows)+15
def cells (s t : Bits) (vs : List Bits) (rows : List (Bits × Bits)) : ℕ :=
  2*rows.length+4+KeptMask.cells s t vs (PackingZeroMask.mask rows)

theorem input_return {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits} {rows : List (Bits × Bits)}
    (hv : Vertices heap a vs) (hc : Context heap b s t rows) (aligned : vs.length=rows.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 200)
    (stack : List (Frame ℕ 200)) (source : Bits) :
    ∃ ext root,ext.length=cells s t vs rows ∧ NaturalRun program (steps s t vs rows)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 170) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (mask s t vs rows) := by
  obtain ⟨ep,sr,tr,table,hb,he,hs,ht,hr⟩ := hc
  let scratch : Cell ℕ := .pair a b
  let h0 := heap++[scratch]
  have hn0 : next+1=h0.length := by simp [h0,hn]
  have hsc : h0[next]?=some scratch := by simp [h0,hn]
  have hb0 : h0[b]?=some (.pair ep table) := lookup_extend hb [scratch]
  obtain ⟨e1,zroot,l1,zrun,zrep⟩ := zero_return (BinaryIndexedPairRead.table_extend hr [scratch])
    (next+1) b next d hn0 ⟨table,b,next,d⟩ 173 (⟨pc,.r3,saved⟩::stack) source
  let h1 := h0++e1
  let n1 := next+1+e1.length
  let savezero : Cell ℕ := .pair next zroot
  let maskctx : Cell ℕ := .pair ep zroot
  let h2 := h1++[savezero,maskctx]
  have hn1 : n1=h1.length := by simp [h1,n1,hn0]
  have hmc : h2[n1+1]?=some maskctx := by simp [h2,hn1]
  have hc2 : KeptMask.Context h2 (n1+1) s t (PackingZeroMask.mask rows) :=
    ⟨ep,sr,tr,zroot,hmc,lookup_extend (lookup_extend (lookup_extend he _) _) _,
      boolList_extend (boolList_extend (boolList_extend hs _) _) _,
      boolList_extend (boolList_extend (boolList_extend ht _) _) _,boolList_extend zrep _⟩
  have hv2 : Vertices h2 a vs := GraphDiscoveryProgram.vertices_extend
    (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend hv _) _) _
  have hn2 : n1+2=h2.length := by simp [h2,hn1]
  obtain ⟨e2,out,l2,mrun,mrep⟩ := mask_return hv2 hc2 (by simpa [PackingZeroMask.mask] using aligned)
    (n1+2) next n1 hn2 ⟨a,n1+1,next,n1⟩ 180 (⟨pc,.r3,saved⟩::stack) source
  refine ⟨[scratch]++e1++[savezero,maskctx]++e2,out,?_,?_,?_⟩
  · simp [cells,l1,l2];omega
  · have hsc1 : (h1++[savezero])[next]?=some scratch := lookup_extend (lookup_extend hsc _) _
    have hb1 : (h1++[savezero])[b]?=some (.pair ep table) := lookup_extend (lookup_extend hb0 _) _
    have hsz : (h1++[savezero])[n1]?=some savezero := by simp [hn1]
    have hsc2 : h2[next]?=some scratch := lookup_extend (lookup_extend hsc _) _
    have t170 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 170)=
        some ⟨(state h0 (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 171),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,scratch]
    have t171 : tickNatural program (state h0 (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 171)=
        some ⟨(state h0 (next+1) table b next d (⟨pc,.r3,saved⟩::stack) source 172),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
    have t172 : tickNatural program (state h0 (next+1) table b next d (⟨pc,.r3,saved⟩::stack) source 172)=
        some ⟨(state h0 (next+1) table b next d (⟨173,.r3,⟨table,b,next,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 30),[],0⟩ := by rfl
    have t173 : tickNatural program (state h1 n1 table b next zroot (⟨pc,.r3,saved⟩::stack) source 173)=
        some ⟨(state (h1++[savezero]) (n1+1) table b next n1 (⟨pc,.r3,saved⟩::stack) source 174),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,savezero]
    have t174 : tickNatural program (state (h1++[savezero]) (n1+1) table b next n1 (⟨pc,.r3,saved⟩::stack) source 174)=
        some ⟨(state (h1++[savezero]) (n1+1) table b next n1 (⟨pc,.r3,saved⟩::stack) source 175),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsc1,scratch]
    have t175 : tickNatural program (state (h1++[savezero]) (n1+1) table b next n1 (⟨pc,.r3,saved⟩::stack) source 175)=
        some ⟨(state (h1++[savezero]) (n1+1) table ep next n1 (⟨pc,.r3,saved⟩::stack) source 176),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
    have t176 : tickNatural program (state (h1++[savezero]) (n1+1) table ep next n1 (⟨pc,.r3,saved⟩::stack) source 176)=
        some ⟨(state (h1++[savezero]) (n1+1) zroot ep next n1 (⟨pc,.r3,saved⟩::stack) source 177),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsz,savezero]
    have t177 : tickNatural program (state (h1++[savezero]) (n1+1) zroot ep next n1 (⟨pc,.r3,saved⟩::stack) source 177)=
        some ⟨(state h2 (n1+2) zroot (n1+1) next n1 (⟨pc,.r3,saved⟩::stack) source 178),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,maskctx,List.append_assoc,Nat.add_assoc]
    have t178 : tickNatural program (state h2 (n1+2) zroot (n1+1) next n1 (⟨pc,.r3,saved⟩::stack) source 178)=
        some ⟨(state h2 (n1+2) a (n1+1) next n1 (⟨pc,.r3,saved⟩::stack) source 179),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hsc2,scratch]
    have t179 : tickNatural program (state h2 (n1+2) a (n1+1) next n1 (⟨pc,.r3,saved⟩::stack) source 179)=
        some ⟨(state h2 (n1+2) a (n1+1) next n1 (⟨180,.r3,⟨a,n1+1,next,n1⟩⟩::⟨pc,.r3,saved⟩::stack) source 162),[],0⟩ := by rfl
    have t180 : tickNatural program (state (h2++e2) (n1+2+e2.length) a (n1+1) next out (⟨pc,.r3,saved⟩::stack) source 180)=
        some ⟨(state (h2++e2) (n1+2+e2.length) saved.a saved.b saved.c out stack source pc),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set]
    have last := run_append mrun (.step t180 (.done _))
    have middle := NaturalRun.step t173 (.step t174 (.step t175 (.step t176 (.step t177 (.step t178 (.step t179 last))))))
    have whole := NaturalRun.step t170 (.step t171 (.step t172 (run_append zrun middle)))
    convert whole using 1 <;> simp [steps,state,h2,h1,h0,n1,List.append_assoc,Nat.add_assoc] <;> omega
  · simpa only [mask,h2,h1,h0,List.append_assoc] using mrep
end DirectedFlowCutGap.KeptMaskInput
