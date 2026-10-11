import DirectedFlowCutGap.PackedBooleanConstructor

/-! A fixed five-instruction program materializes a finite source prefix
as actual heap flags and pairs. An existing counter spine supplies the
length; constructing that spine is a separate preparation obligation. -/
namespace DirectedFlowCutGap.ReferencePrefixMaterialization
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def program : Program 5 := fun pc => match pc.val with
  | 0 => .branch .r1 4 4 4 1
  | 1 => .request .r2 2
  | 2 => .make .r0 (.pair .r2 .r0) 3
  | 3 => .field .r1 .r1 true 0
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 5)) (source : BinaryArithmetic.Bits) (pc : Fin 5) : NaturalState 5 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem materialize {heap : NaturalHeap} {a b q : ℕ} {acc : List Bool}
    (table : BoolList heap a acc) (counter : IndexSpine heap b q)
    (next c d : ℕ) (hn : next = heap.length) (stack : List (Frame ℕ 5))
    (source : BinaryArithmetic.Bits) (enough : q ≤ source.length) :
    ∃ final, NaturalRun program (4*q+1) (state heap next a b c d stack source 0)
      ((source.take q).map Event.request) final ∧
      BoolList final.heap final.registers.a ((source.take q).reverse++acc) ∧
      final.source = source.drop q ∧ final.pc = 4 ∧
      final.heap.length = heap.length+2*q ∧ final.next = next+2*q ∧
      final.stack = stack ∧ tickNatural program final = none := by
  induction q generalizing heap a b acc next c source with
  | zero =>
      cases counter with
      | nil hc =>
          refine ⟨state heap next a b c d stack source 4,?_,?_,rfl,rfl,?_,?_,rfl,?_⟩
          · have step : tickNatural program (state heap next a b c d stack source 0) =
                some ⟨state heap next a b c d stack source 4,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,hc,tagBranch]
            simpa using NaturalRun.step step (NaturalRun.done _)
          · simpa [state] using table
          · simp [state]
          · simp [state]
          · simp [tickNatural,program,state]
  | succ q ih =>
      cases source with
      | nil => simp at enough
      | cons bit rest =>
          cases counter with
          | @cons b payload tail q hc ht =>
              let heap' : NaturalHeap := heap++[.flag bit,.pair next a]
              have hc' : heap'[b]? = some (.pair payload tail) := lookup_extend hc _
              have ht' : IndexSpine heap' tail q := indexSpine_extend ht _
              have flag : heap'[next]? = some (.flag bit) := by
                simp [heap',hn]
              have pair : heap'[next+1]? = some (.pair next a) := by
                simp [heap',hn]
              have table' : BoolList heap' (next+1) (bit::acc) :=
                .cons pair flag (boolList_extend table _)
              have hn' : next+2 = heap'.length := by simp [heap',hn]
              obtain ⟨final,run,rep,src,pc,hlen,alloc,frames,halt⟩ :=
                ih table' ht' (next+2) next hn' rest (by simpa using Nat.le_of_succ_le_succ enough)
              have t0 : tickNatural program (state heap next a b c d stack (bit::rest) 0) =
                  some ⟨state heap next a b c d stack (bit::rest) 1,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,hc,tagBranch]
              have t1 : tickNatural program (state heap next a b c d stack (bit::rest) 1) =
                  some ⟨state (heap++[.flag bit]) (next+1) a b next d stack rest 2,
                    [.request bit],0⟩ := by
                simp [tickNatural,program,state,allocateNatural,Registers.set]
              have t2 : tickNatural program
                  (state (heap++[.flag bit]) (next+1) a b next d stack rest 2) =
                  some ⟨state heap' (next+2) (next+1) b next d stack rest 3,[],0⟩ := by
                simp [tickNatural,program,state,Recipe.cell,allocateNatural,
                  Registers.get,Registers.set,heap',List.append_assoc,Nat.add_assoc]
              have t3 : tickNatural program
                  (state heap' (next+2) (next+1) b next d stack rest 3) =
                  some ⟨state heap' (next+2) (next+1) tail next d stack rest 0,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,Registers.set,hc']
              refine ⟨final,?_,?_,?_,pc,?_,?_,frames,halt⟩
              · simpa [Nat.mul_add,Nat.add_assoc,List.take_succ_cons] using
                  NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t2 (NaturalRun.step t3 run)))
              · simpa [List.take_succ_cons,List.reverse_cons,List.append_assoc] using rep
              · simpa using src
              · simp only [heap',List.length_append,List.length_cons,List.length_nil] at hlen
                omega
              · omega

theorem materialize_high {q : ℕ} {acc : List Bool} (initial : NaturalState 5)
    (pc0 : initial.pc = 0) (hn : initial.next = initial.heap.length)
    (table : BoolList initial.heap initial.registers.a acc)
    (counter : IndexSpine initial.heap initial.registers.b q)
    (enough : q ≤ initial.source.length) :
    ∃ final, NaturalRun program (4*q+1) initial ((initial.source.take q).map Event.request) final ∧
      BoolList final.heap final.registers.a ((initial.source.take q).reverse++acc) ∧
      final.source = initial.source.drop q ∧ final.pc = 4 ∧
      final.heap.length = initial.heap.length+2*q ∧ final.next = initial.next+2*q ∧
      final.stack = initial.stack ∧ tickNatural program final = none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 hn table counter enough
          subst pc
          exact materialize table counter next c d hn stack source enough

/-- The actual bit interpreter pays allocations, reference copying, source
requests, traversal, and its final halt. The same source suffix is retained. -/
theorem materialize_bit {q H B : ℕ} {acc : List Bool} (initial : BitState 5)
    (bounded : initial.Bounded H B) (pc0 : initial.pc = 0)
    (hn : BinaryArithmetic.value initial.next = initial.heap.length)
    (table : BoolList (eraseState initial).heap (eraseState initial).registers.a acc)
    (counter : IndexSpine (eraseState initial).heap (eraseState initial).registers.b q)
    (enough : q ≤ initial.source.length) :
    ∃ charge out, Run program (4*q+1) charge initial
        ((initial.source.take q).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a
        ((initial.source.take q).reverse++acc) ∧
      out.source = initial.source.drop q ∧ out.pc = 4 ∧
      out.Bounded (H+(4*q+1)) (B+(4*q+1)) ∧
      (attempt program out).result = none ∧
      charge+(attempt program out).operations ≤ completeBound 5 H B (4*q+1) := by
  have hn' : (eraseState initial).next = (eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  obtain ⟨final,high,rep,src,pc,_,_,_,halt⟩ :=
    materialize_high (eraseState initial) pc0 hn' table counter enough
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result = none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,source.trans src,?_,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase]; exact rep
  · exact (congrArg State.pc erase).trans pc

end DirectedFlowCutGap.ReferencePrefixMaterialization
