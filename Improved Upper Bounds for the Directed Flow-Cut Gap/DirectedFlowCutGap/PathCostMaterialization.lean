import DirectedFlowCutGap.OutgoingCostProgram
import DirectedFlowCutGap.CanonicalRationalSum

/-! A literal traversal of edge-tail index words builds the outgoing cost
list in the same heap. No precomputed cost records are supplied to this run. -/
namespace DirectedFlowCutGap.PathCostMaterialization
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def label (pc : Fin 111) : Fin 124 := ⟨pc.val,by omega⟩
def program : Program 124 := fun pc =>
  if pc.val=110 then .ret .r3
  else if h : pc.val<111 then
    ReferenceProgramLabels.instruction label (OutgoingCostProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 111 => .branch .r0 112 123 123 114
  | 112 => .make .r3 .nil 113
  | 113 => .ret .r3
  | 114 => .field .r2 .r0 false 115
  | 115 => .field .r0 .r0 true 116
  | 116 => .call 111 117 .r3
  | 117 => .move .r0 .r2 118
  | 118 => .move .r2 .r3 119
  | 119 => .call 109 120 .r3
  | 120 => .make .r3 (.pair .r3 .r2) 121
  | 121 => .ret .r3
  | 122 => .call 111 123 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 124)) (source : Bits) (pc : Fin 124) : NaturalState 124 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

inductive WordList (heap : NaturalHeap) : ℕ → List Bits → Prop
  | nil {p} : heap[p]?=some .nil → WordList heap p []
  | cons {p head tail word words} : heap[p]?=some (.pair head tail) →
      BoolList heap head word → WordList heap tail words → WordList heap p (word::words)

theorem list_extend {heap : NaturalHeap} {p : ℕ} {xs : List Bits}
    (h : WordList heap p xs) (ext : NaturalHeap) : WordList (heap++ext) p xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hx _ ih => exact .cons (lookup_extend hp ext) (boolList_extend hx ext) ih

theorem context_extend {heap : NaturalHeap} {p : ℕ} {rows : List Fraction} {sw : Bits}
    (h : OutgoingCostProgram.Context heap p rows sw) (ext : NaturalHeap) :
    OutgoingCostProgram.Context (heap++ext) p rows sw := by
  obtain ⟨table,word,hp,ht,hw⟩ := h
  exact ⟨table,word,lookup_extend hp ext,BinaryIndexedPairRead.table_extend ht ext,boolList_extend hw ext⟩

def costs (rows : List Fraction) (sw : Bits) (words : List Bits) : List Fraction :=
  words.map (OutgoingCostProgram.result rows sw)

def steps (sw : Bits) : List Bits → ℕ
  | [] => 3
  | word::words => steps sw words+OutgoingCostProgram.instructions sw word+11

def cells (sw : Bits) : List Bits → ℕ
  | [] => 1
  | word::words => cells sw words+OutgoingCostProgram.cells sw word+1

theorem slots (pc : Fin 111) (h : OutgoingCostProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (OutgoingCostProgram.program pc) := by
  by_cases hp : pc.val=110
  · have he : pc=110 := Fin.ext hp
    subst pc;simp [OutgoingCostProgram.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 124} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem outgoing_return {word sw : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (input : BoolList heap a word) (context : OutgoingCostProgram.Context heap b rows sw)
    (hi : value word<rows.length) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 124) (stack : List (Frame ℕ 124)) (source : Bits) :
    ∃ ext root,ext.length=OutgoingCostProgram.cells sw word ∧
      NaturalRun program (OutgoingCostProgram.instructions sw word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 109) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (OutgoingCostProgram.result rows sw word) := by
  obtain ⟨ext,root,len,core,rep⟩ := OutgoingCostProgram.outgoing_high
    (OutgoingCostProgram.state heap next a b c d [] source 109) rfl hn rfl input context hi
  have lift := ReferenceProgramLabels.run label OutgoingCostProgram.program program slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (OutgoingCostProgram.instructions sw word+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 109) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 110) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      OutgoingCostProgram.state,label,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 110)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

/-- Each output record is read or constructed by the actual outgoing subroutine;
the list spine is built by the same recursive traversal. -/
theorem materialize_return {words : List Bits} {sw : Bits} {rows : List Fraction}
    {heap : NaturalHeap} {p : ℕ} (input : WordList heap p words)
    (valid : ∀ word∈words,value word<rows.length) (next b c d : ℕ)
    (hn : next=heap.length) (context : OutgoingCostProgram.Context heap b rows sw)
    (saved : Registers ℕ) (pc : Fin 124) (stack : List (Frame ℕ 124)) (source : Bits) :
    ∃ ext root,ext.length=cells sw words ∧ NaturalRun program (steps sw words)
      (state heap next p b c d (⟨pc,.r3,saved⟩::stack) source 111) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      CanonicalRationalSum.StoredList (heap++ext) root (costs rows sw words) := by
  induction input generalizing next b c d saved pc stack with
  | @nil p hp =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have t111 : tickNatural program (state heap next p b c d frames source 111)=
        some ⟨state heap next p b c d frames source 112,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t112 : tickNatural program (state heap next p b c d frames source 112)=
        some ⟨state (heap++[.nil]) (next+1) p b c next frames source 113,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
    have t113 : tickNatural program (state (heap++[.nil]) (next+1) p b c next frames source 113)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨[.nil],next,rfl,.step t111 (.step t112 (.step t113 (.done _))),.nil (by simp [hn])⟩
  | @cons p head tail word words hp hw ht ih =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have vw : value word<rows.length := valid word (by simp)
    have vs : ∀ w∈words,value w<rows.length := fun w h => valid w (by simp [h])
    obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih vs next b head d hn context ⟨tail,b,head,d⟩ 117 frames
    let h1 := heap++et
    let n1 := next+et.length
    have dense1 : n1=h1.length := by simp [n1,h1,hn]
    obtain ⟨ec,rc,lc,costRun,costRep⟩ := outgoing_return (boolList_extend hw et) (context_extend context et)
      vw n1 rt rt dense1 ⟨head,b,rt,rt⟩ 120 frames source
    let h2 := h1++ec
    let n2 := n1+ec.length
    have dense2 : n2=h2.length := by simp [n2,h2,dense1]
    have t111 : tickNatural program (state heap next p b c d frames source 111)=
        some ⟨state heap next p b c d frames source 114,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t114 : tickNatural program (state heap next p b c d frames source 114)=
        some ⟨state heap next p b head d frames source 115,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t115 : tickNatural program (state heap next p b head d frames source 115)=
        some ⟨state heap next tail b head d frames source 116,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t116 : tickNatural program (state heap next tail b head d frames source 116)=
        some ⟨state heap next tail b head d (⟨117,.r3,⟨tail,b,head,d⟩⟩::frames) source 111,[],0⟩ := by
      simp [tickNatural,program,state]
    have t117 : tickNatural program (state h1 n1 tail b head rt frames source 117)=
        some ⟨state h1 n1 head b head rt frames source 118,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t118 : tickNatural program (state h1 n1 head b head rt frames source 118)=
        some ⟨state h1 n1 head b rt rt frames source 119,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t119 : tickNatural program (state h1 n1 head b rt rt frames source 119)=
        some ⟨state h1 n1 head b rt rt (⟨120,.r3,⟨head,b,rt,rt⟩⟩::frames) source 109,[],0⟩ := by
      simp [tickNatural,program,state]
    have t120 : tickNatural program (state h2 n2 head b rt rc frames source 120)=
        some ⟨state (h2++[.pair rc rt]) (n2+1) head b rt n2 frames source 121,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural]
    have t121 : tickNatural program (state (h2++[.pair rc rt]) (n2+1) head b rt n2 frames source 121)=
        some ⟨state (h2++[.pair rc rt]) (n2+1) saved.a saved.b saved.c n2 stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    have pre : NaturalRun program 4 (state heap next p b c d frames source 111) []
        (state heap next tail b head d (⟨117,.r3,⟨tail,b,head,d⟩⟩::frames) source 111) :=
      .step t111 (.step t114 (.step t115 (.step t116 (.done _))))
    have middle : NaturalRun program 3 (state h1 n1 tail b head rt frames source 117) []
        (state h1 n1 head b rt rt (⟨120,.r3,⟨head,b,rt,rt⟩⟩::frames) source 109) :=
      .step t117 (.step t118 (.step t119 (.done _)))
    refine ⟨et++ec++[.pair rc rt],n2,?_,?_,?_⟩
    · simp [cells,lt,lc,Nat.add_assoc]
    · have all := run_append pre (run_append tailRun (run_append middle
        (run_append costRun (.step t120 (.step t121 (.done _))))))
      convert all using 1 <;> simp [steps,h2,h1,n2,n1,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]; omega
    · have resultRep : CanonicalRationalSum.StoredList (h2++[.pair rc rt]) n2
          (OutgoingCostProgram.result rows sw word::costs rows sw words) :=
        .cons (by simp [dense2]) (stored_extend costRep [.pair rc rt])
          (CanonicalRationalSum.list_extend (CanonicalRationalSum.list_extend tailRep ec) [.pair rc rt])
      simpa [costs,h2,h1,List.append_assoc] using resultRep
theorem materialize_high {words : List Bits} {sw : Bits} {rows : List Fraction} (initial : NaturalState 124)
    (pc0 : initial.pc=122) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : WordList initial.heap initial.registers.a words)
    (context : OutgoingCostProgram.Context initial.heap initial.registers.b rows sw)
    (valid : ∀ word∈words,value word<rows.length) :
    ∃ ext root,ext.length=cells sw words ∧ NaturalRun program (steps sw words+1) initial []
      (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
        initial.registers.b initial.registers.c root [] initial.source 123) ∧
      CanonicalRationalSum.StoredList (initial.heap++ext) root (costs rows sw words) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input context
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 122)=
          some ⟨state heap next a b c d [⟨123,.r3,⟨a,b,c,d⟩⟩] source 111,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep⟩ := materialize_return input valid next b c d hn context ⟨a,b,c,d⟩ 123 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_assoc,state] using NaturalRun.step first run,rep⟩

theorem steps_bound (sw : Bits) (words : List Bits) (B N : ℕ)
    (widths : ∀ w∈words,w.length ≤ B) (indices : ∀ w∈words,value w ≤ N) :
    steps sw words ≤ words.length*(100*(sw.length+B+N+1)+11)+3 := by
  induction words with
  | nil => simp [steps]
  | cons w ws ih =>
    have hh := widths w (by simp)
    have hv := indices w (by simp)
    have rest := ih (fun v h => widths v (by simp [h])) (fun v h => indices v (by simp [h]))
    have cost := OutgoingCostProgram.instructions_bound sw w
    simp only [steps,List.length_cons]
    nlinarith

theorem costs_width (rows : List Fraction) (sw : Bits) (words : List Bits) (B : ℕ)
    (hB : 1 ≤ B) (widths : ∀ x∈rows,StoredBounded x B)
    (indices : ∀ w∈words,value w<rows.length) :
    ∀ x∈costs rows sw words,StoredBounded x B := by
  intro x hx
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
  unfold OutgoingCostProgram.result
  split
  · simp [StoredBounded,zero,hB]
  · have hi := indices w hw
    have hr : IndexedRationalRead.lookup rows w=rows[value w] := by
      simp [IndexedRationalRead.lookup,List.getElem?_eq_getElem hi]
    rw [hr]
    exact widths _ (List.getElem_mem hi)

end DirectedFlowCutGap.PathCostMaterialization
