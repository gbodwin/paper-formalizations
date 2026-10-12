import DirectedFlowCutGap.GraphVertexDecision

/-! The actual pass visits the retained enumeration, omits absent candidates,
and allocates every returned entry and list spine in original vertex order. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def prepend (u : Bits) (q : Option Walk) (xs : List Entry) : List Entry :=
  match q with | none => xs | some w => (u,w)::xs

theorem pass_finish {heap : NaturalHeap} {vertex tail p root : ℕ} {u : Bits}
    {xs : List Entry} {q : Option Walk}
    (word : BoolList heap vertex u) (rest : Table heap tail xs)
    (scratch : heap[p]?=some (.pair vertex tail)) (rep : StoredOption heap root q)
    (next a b : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext out,ext.length=(match q with | none => 0 | some _ => 2) ∧
      NaturalRun program (match q with | none => 3 | some _ => 6)
        (state heap next a b p root (⟨pc,.r3,saved⟩::stack) source 639) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      Table (heap++ext) out (prepend u q xs) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  cases q with
  | none =>
    have nil : heap[root]?=some .nil := rep
    have t639 : tickNatural program (state heap next a b p root frames source 639)=
        some ⟨state heap next a b p root frames source 644,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,nil,tagBranch]
    have t644 : tickNatural program (state heap next a b p root frames source 644)=
        some ⟨state heap next a b p tail frames source 645,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t645 : tickNatural program (state heap next a b p tail frames source 645)=
        some ⟨state heap next saved.a saved.b saved.c tail stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨[],tail,rfl,by simpa using NaturalRun.step t639 (.step t644 (.step t645 (.done _))),
      by simpa [prepend] using rest⟩
  | some q =>
    obtain ⟨es,cost,hroot,he,hcost⟩ := rep
    have walk : StoredWalk heap root q := ⟨es,cost,hroot,he,hcost⟩
    let ext : NaturalHeap := [.pair vertex root,.pair next tail]
    have t639 : tickNatural program (state heap next a b p root frames source 639)=
        some ⟨state heap next a b p root frames source 640,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hroot,tagBranch]
    have t640 : tickNatural program (state heap next a b p root frames source 640)=
        some ⟨state heap next vertex b p root frames source 641,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t641 : tickNatural program (state heap next vertex b p root frames source 641)=
        some ⟨state (heap++[.pair vertex root]) (next+1) next b p root frames source 642,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
    have t642 : tickNatural program (state (heap++[.pair vertex root]) (next+1) next b p root frames source 642)=
        some ⟨state (heap++[.pair vertex root]) (next+1) next b tail root frames source 643,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend scratch [.pair vertex root]]
    have t643 : tickNatural program (state (heap++[.pair vertex root]) (next+1) next b tail root frames source 643)=
        some ⟨state (heap++ext) (next+2) next b tail (next+1) frames source 645,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext,List.append_assoc]
    have t645 : tickNatural program (state (heap++ext) (next+2) next b tail (next+1) frames source 645)=
        some ⟨state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨ext,next+1,rfl,?_,?_⟩
    · exact .step t639 (.step t640 (.step t641 (.step t642 (.step t643 (.step t645 (.done _))))))
    · exact .cons (head:=next) (tail:=tail) (by simp [ext,hn])
        ⟨vertex,root,by simp [ext,hn],boolList_extend word ext,walk_extend walk ext⟩
        (GraphRelaxationProgram.table_extend rest ext)

/-- No discovered output list is supplied: the same real recursive run builds
it from the old table and the represented enumeration. -/
theorem pass_return {heap : NaturalHeap} {a b : ℕ} {us : List Bits} {target sw : Bits}
    {adjacency : List Bits} {rows : List Fraction} {old : List Entry}
    (vertices : Vertices heap a us) (context : Context heap b adjacency rows sw target old)
    (hi : ∀ u∈us,value u<adjacency.length) (hc : ∀ u∈us,value u<rows.length)
    (hcols : ∀ u,(hu : u∈us) → ∀ x∈old,value x.1<(adjacency[value u]'(hi u hu)).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=passCells adjacency rows sw target old us ∧
      NaturalRun program (passSteps adjacency rows sw target old us)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 630) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Table (heap++ext) root (pass adjacency rows sw target old us) := by
  induction vertices generalizing c saved pc stack with
  | @nil p hp =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have t630 : tickNatural program (state heap next p b c d frames source 630)=
        some ⟨state heap next p b c d frames source 631,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t631 : tickNatural program (state heap next p b c d frames source 631)=
        some ⟨state (heap++[.nil]) (next+1) p b c next frames source 632,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
    have t632 : tickNatural program (state (heap++[.nil]) (next+1) p b c next frames source 632)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨[.nil],next,rfl,?_,.nil ?_⟩
    · exact .step t630 (.step t631 (.step t632 (.done _)))
    · simp [hn]
  | @cons p head tail u us hp hu ht ih =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    obtain ⟨et,rt,lt,runT,repT⟩ := ih
      (fun v hv => hi v (by simp [hv])) (fun v hv => hc v (by simp [hv]))
      (fun v hv => hcols v (by simp [hv])) head ⟨tail,b,head,d⟩ 636 frames
    let h0 := heap++et
    let n0 := next+et.length
    let e0 : NaturalHeap := [.pair head rt]
    let h1 := h0++e0
    let n1 := n0+1
    have dense0 : n0=h0.length := by simp [h0,n0,hn]
    have dense1 : n1=h1.length := by simp [h1,n1,e0,dense0]
    have scratch : h1[n0]?=some (.pair head rt) := by simp [h1,e0,dense0]
    obtain ⟨ev,rv,lv,runV,repV⟩ := vertex_return
      (boolList_extend (boolList_extend hu et) e0)
      (context_extend (context_extend context et) e0)
      (hi u (by simp)) (hc u (by simp)) (hcols u (by simp))
      n1 n0 rt dense1 ⟨head,b,n0,rt⟩ 639 frames source
    let h2 := h1++ev
    let n2 := n1+ev.length
    have dense2 : n2=h2.length := by simp [h2,n2,dense1]
    obtain ⟨ef,rf,lf,runF,repF⟩ := pass_finish
      (boolList_extend (boolList_extend (boolList_extend hu et) e0) ev)
      (GraphRelaxationProgram.table_extend (GraphRelaxationProgram.table_extend repT e0) ev)
      (lookup_extend scratch ev) repV n2 head b dense2 saved pc stack source
    have t630 : tickNatural program (state heap next p b c d frames source 630)=
        some ⟨state heap next p b c d frames source 633,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t633 : tickNatural program (state heap next p b c d frames source 633)=
        some ⟨state heap next p b head d frames source 634,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t634 : tickNatural program (state heap next p b head d frames source 634)=
        some ⟨state heap next tail b head d frames source 635,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t635 : tickNatural program (state heap next tail b head d frames source 635)=
        some ⟨state heap next tail b head d (⟨636,.r3,⟨tail,b,head,d⟩⟩::frames) source 630,[],0⟩ := by
      simp [tickNatural,program,state]
    have t636 : tickNatural program (state h0 n0 tail b head rt frames source 636)=
        some ⟨state h1 n1 tail b n0 rt frames source 637,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1,n1,e0]
    have t637 : tickNatural program (state h1 n1 tail b n0 rt frames source 637)=
        some ⟨state h1 n1 head b n0 rt frames source 638,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t638 : tickNatural program (state h1 n1 head b n0 rt frames source 638)=
        some ⟨state h1 n1 head b n0 rt (⟨639,.r3,⟨head,b,n0,rt⟩⟩::frames) source 600,[],0⟩ := by
      simp [tickNatural,program,state]
    let ext := et++e0++ev++ef
    have shape : heap++ext=h2++ef := by simp [ext,h2,h1,h0,List.append_assoc]
    have count : next+ext.length=n2+ef.length := by simp [ext,n2,n1,n0,e0];omega
    refine ⟨ext,rf,?_,?_,?_⟩
    · simp only [ext,List.length_append,lt,lv,lf,e0,List.length_cons,List.length_nil,passCells]
      cases atVertex adjacency rows sw target u old <;> simp only
    · have first := NaturalRun.step t630 (.step t633 (.step t634 (.step t635 runT)))
      have second := NaturalRun.step t636 (.step t637 (.step t638 (run_append runV runF)))
      rw [shape,count]
      convert run_append first second using 1
      simp only [passSteps]
      cases atVertex adjacency rows sw target u old <;> simp <;> omega
      all_goals rfl
    · rw [shape]
      change Table (h2++ef) rf (prepend u (atVertex adjacency rows sw target u old)
        (pass adjacency rows sw target old us))
      exact repF

end DirectedFlowCutGap.GraphDiscoveryProgram
