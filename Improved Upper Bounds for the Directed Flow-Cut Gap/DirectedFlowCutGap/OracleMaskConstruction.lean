import DirectedFlowCutGap.OracleMaskVertex

namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def steps (s t : Bits) (es : List (Bits × Bits)) : List Bits → ℕ
  | [] => 3
  | u::us => steps s t es us+bitSteps s t u es+11
def cells (s t : Bits) (es : List (Bits × Bits)) : List Bits → ℕ
  | [] => 1
  | u::us => cells s t es us+bitCells s t u es+2

theorem cons_return {heap : NaturalHeap} {p word tail rt b : ℕ} {s t u : Bits}
    {es : List (Bits × Bits)} {bs : Bits} (node : heap[p]?=some (.pair word tail))
    (hu : BoolList heap word u) (hc : Context heap b s t es) (ht : BoolList heap rt bs)
    (next a : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 160) (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root,ext.length=bitCells s t u es+2 ∧ NaturalRun program (bitSteps s t u es+7)
      (state heap next a b p rt (⟨pc,.r3,saved⟩::stack) source 126) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (bit s t u es::bs) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair p rt]
  obtain ⟨e1,flag,len1,body,out⟩ := bit_return (boolList_extend hu e0) (context_extend hc e0)
    (next+1) next rt (by simp [e0,hn]) ⟨word,b,next,rt⟩ 130 frames source
  let n1 := next+1+e1.length
  have t126 : tickNatural program (state heap next a b p rt frames source 126)=
      some ⟨state (heap++e0) (next+1) a b next rt frames source 127,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e0]
  have t127 : tickNatural program (state (heap++e0) (next+1) a b next rt frames source 127)=
      some ⟨state (heap++e0) (next+1) p b next rt frames source 128,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,e0,hn]
  have t128 : tickNatural program (state (heap++e0) (next+1) p b next rt frames source 128)=
      some ⟨state (heap++e0) (next+1) word b next rt frames source 129,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend node e0]
  have t129 : tickNatural program (state (heap++e0) (next+1) word b next rt frames source 129)=
      some ⟨state (heap++e0) (next+1) word b next rt
        (⟨130,.r3,⟨word,b,next,rt⟩⟩::frames) source 90,[],0⟩ := by
    simp [tickNatural,program,state]
  have t130 : tickNatural program (state ((heap++e0)++e1) n1 word b next flag frames source 130)=
      some ⟨state ((heap++e0)++e1) n1 word b rt flag frames source 131,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,e0,hn,List.append_assoc]
  have t131 : tickNatural program (state ((heap++e0)++e1) n1 word b rt flag frames source 131)=
      some ⟨state (((heap++e0)++e1)++[.pair flag rt]) (n1+1) word b rt n1 frames source 132,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
  have t132 : tickNatural program
      (state (((heap++e0)++e1)++[.pair flag rt]) (n1+1) word b rt n1 frames source 132)=
      some ⟨state (((heap++e0)++e1)++[.pair flag rt]) (n1+1)
        saved.a saved.b saved.c n1 stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨e0++e1++[.pair flag rt],n1,by simp [e0,len1],?_,?_⟩
  · have all := NaturalRun.step t126 (.step t127 (.step t128 (.step t129
      (run_append body (.step t130 (.step t131 (.step t132 (.done _))))))))
    convert all using 1 <;> simp [state,e0,n1,List.append_assoc]
    all_goals omega
  · apply BoolList.cons (head:=flag) (tail:=rt)
    · have hn1 : n1=((heap++e0)++e1).length := by simp [n1,e0,hn];omega
      have hp : (((heap++e0)++e1)++[.pair flag rt])[n1]?=some (.pair flag rt) := by rw [hn1];simp
      simpa [List.append_assoc] using hp
    · simpa [List.append_assoc] using lookup_extend out [.pair flag rt]
    · exact boolList_extend ht _

theorem mask_return {heap : NaturalHeap} {p : ℕ} {vs : List Bits} {s t : Bits}
    {es : List (Bits × Bits)} (input : GraphDiscoveryProgram.Vertices heap p vs)
    (next b c d : ℕ) (hn : next=heap.length) (context : Context heap b s t es)
    (saved : Registers ℕ) (pc : Fin 160) (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root,ext.length=cells s t es vs ∧ NaturalRun program (steps s t es vs)
      (state heap next p b c d (⟨pc,.r3,saved⟩::stack) source 120) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (mask s t es vs) := by
  induction input generalizing next b c d saved pc stack with
  | @nil p hp =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have t120 : tickNatural program (state heap next p b c d frames source 120)=
        some ⟨state heap next p b c d frames source 121,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t121 : tickNatural program (state heap next p b c d frames source 121)=
        some ⟨state (heap++[.nil]) (next+1) p b c next frames source 122,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
    have t122 : tickNatural program (state (heap++[.nil]) (next+1) p b c next frames source 122)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨[.nil],next,rfl,.step t120 (.step t121 (.step t122 (.done _))),.nil (by simp [hn])⟩
  | @cons p head tail u us hp hu _ ih =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih next b p d hn context ⟨tail,b,p,d⟩ 126 frames
    obtain ⟨eh,rh,lh,headRun,headRep⟩ := cons_return (lookup_extend hp et) (boolList_extend hu et)
      (context_extend context et) tailRep (next+et.length) tail (by simp [hn]) saved pc stack source
    have t120 : tickNatural program (state heap next p b c d frames source 120)=
        some ⟨state heap next p b c d frames source 123,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t123 : tickNatural program (state heap next p b c d frames source 123)=
        some ⟨state heap next p b p d frames source 124,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t124 : tickNatural program (state heap next p b p d frames source 124)=
        some ⟨state heap next tail b p d frames source 125,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t125 : tickNatural program (state heap next tail b p d frames source 125)=
        some ⟨state heap next tail b p d (⟨126,.r3,⟨tail,b,p,d⟩⟩::frames) source 120,[],0⟩ := by
      simp [tickNatural,program,state]
    refine ⟨et++eh,rh,by simp [cells,lt,lh,Nat.add_assoc],?_,?_⟩
    · have all := run_append (.step t120 (.step t123 (.step t124 (.step t125 tailRun)))) headRun
      convert all using 1 <;> simp [steps,List.append_assoc,state]
      all_goals omega
    · simpa [mask,List.append_assoc] using headRep

end DirectedFlowCutGap.OracleMask
