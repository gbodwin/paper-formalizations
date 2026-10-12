import DirectedFlowCutGap.PackingUpdateRowTail

namespace DirectedFlowCutGap.PackingUpdateRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_return (amount : Fraction) {cs ys : List Fraction} {mask : List Bool}
    {heap : NaturalHeap} {a b ctx mr ar : ℕ}
    (cap : StoredList heap a cs) (weights : StoredList heap b ys)
    (flags : BoolList heap mr mask) (amt : Stored heap ar amount)
    (context : heap[ctx]?=some (.pair mr ar))
    (aligned : cs.length=ys.length) (alignedMask : cs.length=mask.length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 520) (stack : List (Frame ℕ 520)) (source : Bits) :
    ∃ ext root,ext.length=cells amount cs ys mask ∧
      NaturalRun program (steps amount cs ys mask)
        (state heap next a b ctx d (⟨pc,.r0,saved⟩::stack) source 480) []
        (state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc) ∧
      StoredList (heap++ext) root (result amount cs ys mask) := by
  induction cs generalizing ys mask heap a b ctx mr ar next d saved pc stack with
  | nil =>
    have hy : ys=[] := by simpa using aligned.symm
    have hm : mask=[] := by simpa using alignedMask.symm
    subst ys;subst mask
    cases cap with
    | nil hp =>
      let frames : List (Frame ℕ 520) := ⟨pc,.r0,saved⟩::stack
      have t480 : tickNatural program (state heap next a b ctx d frames source 480)=
          some ⟨state heap next a b ctx d frames source 481,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t481 : tickNatural program (state heap next a b ctx d frames source 481)=
          some ⟨state (heap++[.nil]) (next+1) a b ctx next frames source 482,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural]
      have t482 : tickNatural program (state (heap++[.nil]) (next+1) a b ctx next frames source 482)=
          some ⟨state (heap++[.nil]) (next+1) next saved.b saved.c saved.d stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,frames]
      exact ⟨[.nil],next,rfl,.step t480 (.step t481 (.step t482 (.done _))),.nil (by simp [hn])⟩
  | cons ci cs ih =>
    cases ys with
    | nil => simp at aligned
    | cons y ys =>
      cases mask with
      | nil => simp at alignedMask
      | cons enabled fs =>
        have al : cs.length=ys.length := by simpa using aligned
        have am : cs.length=fs.length := by simpa using alignedMask
        cases cap with
        | @cons a ca ct ci cs hc cr ctail =>
          cases weights with
          | @cons b ya yt y ys hy yr ytail =>
            cases flags with
            | @cons mr mf mt enabled fs hm hf ftail =>
              let frames : List (Frame ℕ 520) := ⟨pc,.r0,saved⟩::stack
              obtain ⟨eh,rh,rb,rc,lh,headRun,headRep,original,frame⟩ :=
                head_high (d:=d) ci amount y enabled hc hy context hm hf cr amt yr hn frames source
              let hh := heap++eh
              let nh := next+eh.length
              have denseH : nh=hh.length := by simp [nh,hh,hn]
              let ep : NaturalHeap := [.pair rh (next+1),.pair mt ar]
              let hp := hh++ep
              let np := nh+2
              have prep := tail_prepare (head:=rh) (rb:=rb) (rc:=rc) frame original
                (lookup_extend context eh) (lookup_extend hm eh)
                (lookup_extend hc eh) (lookup_extend hy eh) denseH frames source
              have denseP : np=hp.length := by simp [np,hp,ep,denseH]
              have ctxP : hp[nh+1]?=some (.pair mt ar) := by simp [hp,ep,denseH]
              obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih
                (list_extend (list_extend ctail eh) ep)
                (list_extend (list_extend ytail eh) ep)
                (boolList_extend (boolList_extend ftail eh) ep)
                (stored_extend (stored_extend amt eh) ep) ctxP al am
                np nh denseP ⟨ct,yt,nh+1,nh⟩ 513 frames
              let ht := hp++et
              let nt := np+et.length
              have denseT : nt=ht.length := by simp [nt,ht,denseP]
              have frameT : ht[nh]?=some (.pair rh (next+1)) := by
                apply lookup_extend
                simp [hp,ep,denseH]
              obtain ⟨finish,rep⟩ := cons_return (b:=yt) (c:=nh+1) frameT
                (stored_extend (stored_extend headRep ep) et) tailRep denseT saved pc stack source
              let ef : NaturalHeap := [.pair rh rt]
              let ext := eh++ep++et++ef
              have heaps : heap++ext=ht++ef := by simp [ext,ht,hp,hh,List.append_assoc]
              have sizes : next+ext.length=nt+1 := by simp [ext,nt,np,nh,ep,ef];omega
              have whole := run_append headRun (run_append prep (run_append tailRun finish))
              refine ⟨ext,nt,?_,?_,?_⟩
              · simp [ext,ep,ef,cells,lh,lt]
                split <;> omega
              · rw [heaps,sizes]
                convert whole using 1 <;> simp [steps]
                split <;> omega
              · rw [heaps]
                simpa [result,ef] using rep
end DirectedFlowCutGap.PackingUpdateRow
