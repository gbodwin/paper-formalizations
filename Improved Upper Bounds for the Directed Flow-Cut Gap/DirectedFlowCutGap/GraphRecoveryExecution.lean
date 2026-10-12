import DirectedFlowCutGap.GraphRecoveryFinish

namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem shortest_return {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {values : List Fraction} {sw target u : Bits} (N : ℕ)
    (input : GraphDiscoveryProgram.Vertices heap a vs)
    (context : GraphDiscoveryProgram.GlobalContext heap b vs adjacency values sw target)
    (word : BoolList heap c u) (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (ht : value target<N) (hc : ∀ v∈vs,value v<values.length)
    (valid : ∀ q,GraphDiscoveryProgram.minimize vs adjacency values sw target u=some q →
      ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges sw target).map Prod.fst,value w<values.length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1344)
    (stack : List (Frame ℕ 1344)) (source : Bits) :
    ∃ ext root,ext.length=cells vs adjacency values sw target u ∧
      NaturalRun program (steps vs adjacency values sw target u)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1312) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root (result vs adjacency values sw target u) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  have hi : ∀ v∈vs,value v<adjacency.length := fun v h => lt_of_lt_of_le (hv v h) rows
  have targetCol : ∀ v,(h : v∈vs) → value target<(adjacency[value v]'(hi v h)).length :=
    fun v h => lt_of_lt_of_le ht (cols (value v) (hv v h))
  have columns : ∀ v,(h : v∈vs) → ∀ z∈vs,value z<(adjacency[value v]'(hi v h)).length :=
    fun v h z hz => lt_of_lt_of_le (hv z hz) (cols (value v) (hv v h))
  obtain ⟨ed,chosen,ld,discover,rep⟩ := discovery_call input context word hi hc targetCol columns
    next d hn ⟨a,b,c,d⟩ 1313 frames source
  obtain ⟨er,root,lr,recover,outRep⟩ := finish_return N (GraphDiscoveryProgram.global_extend context ed)
    rep rows cols hv ht valid (next+ed.length) a c (by simp [hn]) saved pc stack source
  have first : tickNatural program (state heap next a b c d frames source 1312)=
      some ⟨state heap next a b c d (⟨1313,.r3,⟨a,b,c,d⟩⟩::frames) source 717,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨ed++er,root,by simp [cells,ld,lr],?_,?_⟩
  · have all := run_append (.step first discover) recover
    convert all using 1 <;> simp [steps,List.append_assoc,Nat.add_assoc,Nat.add_comm];omega
  · simpa only [result,List.append_assoc] using outRep

theorem shortest_high {vs adjacency : List Bits} {values : List Fraction} {sw target u : Bits}
    (N : ℕ) (initial : NaturalState 1344) (pc0 : initial.pc=1342)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : GraphDiscoveryProgram.Vertices initial.heap initial.registers.a vs)
    (context : GraphDiscoveryProgram.GlobalContext initial.heap initial.registers.b vs adjacency values sw target)
    (word : BoolList initial.heap initial.registers.c u) (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (ht : value target<N) (hc : ∀ v∈vs,value v<values.length)
    (valid : ∀ q,GraphDiscoveryProgram.minimize vs adjacency values sw target u=some q →
      ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges sw target).map Prod.fst,value w<values.length) :
    ∃ ext root,ext.length=cells vs adjacency values sw target u ∧
      NaturalRun program (steps vs adjacency values sw target u+1) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a initial.registers.b
          initial.registers.c root [] initial.source 1343) ∧
      GraphDiscoveryProgram.StoredOption (initial.heap++ext) root (result vs adjacency values sw target u) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input context word
      subst pc;subst stack
      obtain ⟨ext,root,len,body,rep⟩ := shortest_return N input context word rows cols hv ht hc valid
        next d hn ⟨a,b,c,d⟩ 1343 [] source
      have first : tickNatural program (state heap next a b c d [] source 1342)=
          some ⟨state heap next a b c d [⟨1343,.r3,⟨a,b,c,d⟩⟩] source 1312,[],0⟩ := by
        simp [tickNatural,program,state]
      exact ⟨ext,root,len,by simpa [state] using NaturalRun.step first body,rep⟩

end DirectedFlowCutGap.GraphRecoveryController
