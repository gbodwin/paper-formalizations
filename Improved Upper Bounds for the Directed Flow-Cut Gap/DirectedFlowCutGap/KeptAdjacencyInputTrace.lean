import DirectedFlowCutGap.KeptAdjacencyInputCalls

namespace DirectedFlowCutGap.KeptAdjacencyInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def kept (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) : Bits := KeptMaskInput.mask s t vs costs

def result (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : List Bits :=
  KeptAdjacencyMatrix.matrix (kept s t vs costs) rows (kept s t vs costs)
def steps (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : ℕ :=
  KeptMaskInput.steps s t vs costs+KeptAdjacencyMatrix.steps (kept s t vs costs) rows (kept s t vs costs)+12
def cells (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : ℕ :=
  KeptMaskInput.cells s t vs costs+KeptAdjacencyMatrix.cells (kept s t vs costs) rows (kept s t vs costs)+2

theorem mask_length (s t : Bits) (vs : List Bits) (zs : Bits) (aligned : vs.length=zs.length) :
    (KeptMask.mask s t vs zs).length=vs.length := by
  induction vs generalizing zs with
  | nil => cases zs <;> simp_all [KeptMask.mask]
  | cons u us ih =>
    cases zs with
    | nil => simp at aligned
    | cons z zs => simpa [KeptMask.mask] using ih zs (by simpa using aligned)

theorem kept_length (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (aligned : vs.length=costs.length) :
    (kept s t vs costs).length=vs.length := by
  apply mask_length
  simpa [PackingZeroMask.mask] using aligned

theorem input_return {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits}
    {costs : List (Bits × Bits)} {rows : List Bits}
    (hv : Vertices heap a vs) (hc : Context heap b s t costs rows)
    (aligned : vs.length=costs.length) (height : rows.length=vs.length)
    (widths : ∀ u∈rows,u.length=vs.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 320)
    (stack : List (Frame ℕ 320)) (source : Bits) :
    ∃ ext root,ext.length=cells s t vs costs rows ∧ NaturalRun program (steps s t vs costs rows)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 290) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Matrix (heap++ext) root (result s t vs costs rows) := by
  obtain ⟨mc,ar,hb,hm,ha⟩ := hc
  let scratch : Cell ℕ := .pair a b
  let h0 := heap++[scratch]
  have hn0 : next+1=h0.length := by simp [h0,hn]
  have hsc : h0[next]?=some scratch := by simp [h0,hn]
  have hb0 : h0[b]?=some (.pair mc ar) := lookup_extend hb [scratch]
  obtain ⟨e1,kroot,l1,krun,krep⟩ := mask_return (GraphDiscoveryProgram.vertices_extend hv [scratch])
    (KeptMaskInput.context_extend hm [scratch]) aligned (next+1) next d hn0 ⟨a,mc,next,d⟩ 293
    (⟨pc,.r3,saved⟩::stack) source
  let h1 := h0++e1
  let n1 := next+1+e1.length
  let matrixctx : Cell ℕ := .pair kroot kroot
  let h2 := h1++[matrixctx]
  have hn1 : n1=h1.length := by simp [h1,n1,hn0]
  have hmc : h2[n1]?=some matrixctx := by simp [h2,hn1]
  have hc2 : KeptAdjacencyMatrix.Context h2 n1 (kept s t vs costs) (kept s t vs costs) :=
    ⟨kroot,kroot,hmc,boolList_extend krep _,boolList_extend krep _⟩
  have ha2 : Matrix h2 ar rows := GraphDiscoveryProgram.vertices_extend
    (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend ha _) _) _
  have hn2 : n1+1=h2.length := by simp [h2,hn1]
  have hlen := kept_length s t vs costs aligned
  obtain ⟨e2,out,l2,mrun,mrep⟩ := matrix_return ha2 hc2 (by omega)
    (fun u hu => (widths u hu).trans hlen.symm) (n1+1) next kroot hn2 ⟨ar,n1,next,kroot⟩ 297
    (⟨pc,.r3,saved⟩::stack) source
  refine ⟨[scratch]++e1++[matrixctx]++e2,out,?_,?_,?_⟩
  · simp [cells,l1,l2];omega
  · have hsc2 : h2[next]?=some scratch := lookup_extend (lookup_extend hsc _) _
    have hb2 : h2[b]?=some (.pair mc ar) := lookup_extend (lookup_extend hb0 _) _
    have t290 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 290)=
        some ⟨state h0 (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 291,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,scratch]
    have t291 : tickNatural program (state h0 (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 291)=
        some ⟨state h0 (next+1) a mc next d (⟨pc,.r3,saved⟩::stack) source 292,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
    have t292 : tickNatural program (state h0 (next+1) a mc next d (⟨pc,.r3,saved⟩::stack) source 292)=
        some ⟨state h0 (next+1) a mc next d (⟨293,.r3,⟨a,mc,next,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 198,[],0⟩ := by rfl
    have t293 : tickNatural program (state h1 n1 a mc next kroot (⟨pc,.r3,saved⟩::stack) source 293)=
        some ⟨state h2 (n1+1) a n1 next kroot (⟨pc,.r3,saved⟩::stack) source 294,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,matrixctx]
    have t294 : tickNatural program (state h2 (n1+1) a n1 next kroot (⟨pc,.r3,saved⟩::stack) source 294)=
        some ⟨state h2 (n1+1) b n1 next kroot (⟨pc,.r3,saved⟩::stack) source 295,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hsc2,scratch]
    have t295 : tickNatural program (state h2 (n1+1) b n1 next kroot (⟨pc,.r3,saved⟩::stack) source 295)=
        some ⟨state h2 (n1+1) ar n1 next kroot (⟨pc,.r3,saved⟩::stack) source 296,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hb2]
    have t296 : tickNatural program (state h2 (n1+1) ar n1 next kroot (⟨pc,.r3,saved⟩::stack) source 296)=
        some ⟨state h2 (n1+1) ar n1 next kroot (⟨297,.r3,⟨ar,n1,next,kroot⟩⟩::⟨pc,.r3,saved⟩::stack) source 282,[],0⟩ := by rfl
    have t297 : tickNatural program (state (h2++e2) (n1+1+e2.length) ar n1 next out (⟨pc,.r3,saved⟩::stack) source 297)=
        some ⟨state (h2++e2) (n1+1+e2.length) saved.a saved.b saved.c out stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have last := run_append mrun (.step t297 (.done _))
    have middle := NaturalRun.step t293 (.step t294 (.step t295 (.step t296 last)))
    have whole := NaturalRun.step t290 (.step t291 (.step t292 (run_append krun middle)))
    convert whole using 1 <;> simp [steps,kept,state,h2,h1,h0,n1,List.append_assoc,Nat.add_assoc] <;> omega
  · simpa only [result,h2,h1,h0,List.append_assoc] using mrep
end DirectedFlowCutGap.KeptAdjacencyInput
