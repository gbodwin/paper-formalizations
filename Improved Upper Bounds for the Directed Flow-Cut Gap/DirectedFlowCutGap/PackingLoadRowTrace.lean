import DirectedFlowCutGap.PackingLoadRowTail

namespace DirectedFlowCutGap.PackingLoadRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_return (amount : Fraction) {ys : List Fraction} {mask : List Bool}
    {heap : NaturalHeap} {a ctx mr ar : ℕ}
    (loads : StoredList heap a ys) (flags : BoolList heap mr mask) (amt : Stored heap ar amount)
    (context : heap[ctx]?=some (.pair mr ar)) (aligned : ys.length=mask.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 200) (stack : List (Frame ℕ 200)) (source : Bits) :
    ∃ ext root,ext.length=cells amount ys mask ∧
      NaturalRun program (steps amount ys mask)
        (state heap next a ctx c d (⟨pc,.r0,saved⟩::stack) source 160) []
        (state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc) ∧
      StoredList (heap++ext) root (result amount ys mask) := by
  induction ys generalizing mask heap a ctx mr ar next c d saved pc stack with
  | nil =>
    have hm : mask=[] := by simpa using aligned.symm
    subst mask
    cases loads with
    | nil hp =>
      let frames : List (Frame ℕ 200) := ⟨pc,.r0,saved⟩::stack
      have t160 : tickNatural program (state heap next a ctx c d frames source 160)=
          some ⟨state heap next a ctx c d frames source 161,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t161 : tickNatural program (state heap next a ctx c d frames source 161)=
          some ⟨state (heap++[.nil]) (next+1) a ctx c next frames source 162,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural]
      have t162 : tickNatural program (state (heap++[.nil]) (next+1) a ctx c next frames source 162)=
          some ⟨state (heap++[.nil]) (next+1) next saved.b saved.c saved.d stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,frames]
      exact ⟨[.nil],next,rfl,.step t160 (.step t161 (.step t162 (.done _))),.nil (by simp [hn])⟩
  | cons y ys ih =>
    cases mask with
    | nil => simp at aligned
    | cons enabled fs =>
      have al : ys.length=fs.length := by simpa using aligned
      cases loads with
      | @cons a ya yt y ys hy yr ytail =>
        cases flags with
        | @cons mr mf mt enabled fs hm hf ftail =>
          let frames : List (Frame ℕ 200) := ⟨pc,.r0,saved⟩::stack
          obtain ⟨eh,rh,lh,headRun,headRep,frame⟩ :=
            head_high (c:=c) (d:=d) enabled amount y hy context hm hf yr amt hn frames source
          let hh := heap++eh
          let nh := next+eh.length
          have denseH : nh=hh.length := by simp [nh,hh,hn]
          let ep : NaturalHeap := [.pair rh next,.pair mt ar]
          let hp := hh++ep
          let np := nh+2
          have prep := tail_prepare (head:=rh) (rb:=ar) (rc:=mf) frame
            (lookup_extend context eh) (lookup_extend hm eh) (lookup_extend hy eh) denseH frames source
          have denseP : np=hp.length := by simp [np,hp,ep,denseH]
          have ctxP : hp[nh+1]?=some (.pair mt ar) := by simp [hp,ep,denseH]
          obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih
            (list_extend (list_extend ytail eh) ep)
            (boolList_extend (boolList_extend ftail eh) ep)
            (stored_extend (stored_extend amt eh) ep) ctxP al
            np next nh denseP ⟨yt,nh+1,next,nh⟩ 179 frames
          let ht := hp++et
          let nt := np+et.length
          have denseT : nt=ht.length := by simp [nt,ht,denseP]
          have frameT : ht[nh]?=some (.pair rh next) := by
            apply lookup_extend
            simp [hp,ep,denseH]
          obtain ⟨finish,rep⟩ := cons_return (b:=nh+1) (c:=next) frameT
            (stored_extend (stored_extend headRep ep) et) tailRep denseT saved pc stack source
          let ef : NaturalHeap := [.pair rh rt]
          let ext := eh++ep++et++ef
          have heaps : heap++ext=ht++ef := by simp [ext,ht,hp,hh,List.append_assoc]
          have sizes : next+ext.length=nt+1 := by simp [ext,nt,np,nh,ep,ef];omega
          have whole := run_append headRun (run_append prep (run_append tailRun finish))
          refine ⟨ext,nt,?_,?_,?_⟩
          · simp [ext,ep,ef,cells,lh,lt];omega
          · rw [heaps,sizes]
            convert whole using 1 <;> simp [steps]
            omega
          · rw [heaps]
            simpa [result,ef] using rep
end DirectedFlowCutGap.PackingLoadRow
