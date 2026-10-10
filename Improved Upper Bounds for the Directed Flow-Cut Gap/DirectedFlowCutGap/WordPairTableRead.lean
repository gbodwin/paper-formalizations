import DirectedFlowCutGap.PackedBooleanConstructor

/-! A concrete immutable-reference read of a table of two-word records.
The result retains the actual numerator/denominator references rather than
materializing or silently decoding their payloads. Whole graph substitution
and construction of the record-table representation remain separate. -/
namespace DirectedFlowCutGap.WordPairTableRead
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

inductive Table (heap : NaturalHeap) : ℕ → List (Bits × Bits) → Prop
  | nil {root : ℕ} : heap[root]? = some .nil → Table heap root []
  | cons {root item tail num den : ℕ} {a b : Bits} {rest : List (Bits × Bits)} :
      heap[root]? = some (.pair item tail) → heap[item]? = some (.pair num den) →
      BoolList heap num a → BoolList heap den b → Table heap tail rest →
      Table heap root ((a,b)::rest)

def program : Program 7 := fun pc => match pc.val with
  | 0 => .branch .r1 3 6 6 1
  | 1 => .field .r0 .r0 true 2
  | 2 => .field .r1 .r1 true 0
  | 3 => .field .r2 .r0 false 4
  | 4 => .field .r0 .r2 false 5
  | 5 => .field .r1 .r2 true 6
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 7)) (source : Bits) (pc : Fin 7) : NaturalState 7 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

/-- Both returned addresses name the selected stored words in the very same
heap. No input-dependent object is hidden in the fixed instruction table. -/
theorem read {heap : NaturalHeap} {a b i : ℕ} {rows : List (Bits × Bits)}
    (table : Table heap a rows) (index : IndexSpine heap b i) (hi : i < rows.length)
    (next c d : ℕ) (stack : List (Frame ℕ 7)) (source : Bits) :
    ∃ num den item, NaturalRun program (3*i+4)
        (state heap next a b c d stack source 0) []
        (state heap next num den item d stack source 6) ∧
      BoolList heap num rows[i].1 ∧ BoolList heap den rows[i].2 := by
  induction i generalizing a b rows c with
  | zero =>
      cases index with
      | nil hc =>
          cases table with
          | nil ht => simp at hi
          | @cons root item tail num den x y rest ht hv hx hy hr =>
              refine ⟨num,den,item,?_,hx,hy⟩
              have t0 : tickNatural program (state heap next a b c d stack source 0) =
                  some ⟨state heap next a b c d stack source 3,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,hc,tagBranch]
              have t3 : tickNatural program (state heap next a b c d stack source 3) =
                  some ⟨state heap next a b item d stack source 4,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,Registers.set,ht]
              have t4 : tickNatural program (state heap next a b item d stack source 4) =
                  some ⟨state heap next num b item d stack source 5,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,Registers.set,hv]
              have t5 : tickNatural program (state heap next num b item d stack source 5) =
                  some ⟨state heap next num den item d stack source 6,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,Registers.set,hv]
              simpa using NaturalRun.step t0 (NaturalRun.step t3
                (NaturalRun.step t4 (NaturalRun.step t5 (NaturalRun.done _))))
  | succ i ih =>
      cases index with
      | @cons b payload btail i hb htail =>
          cases table with
          | nil ht => simp at hi
          | @cons root item tail num den x y rest ht hv hx hy hr =>
              have hi' : i < rest.length := by simpa using hi
              obtain ⟨n',d',item',run,ra,rb⟩ := ih hr htail hi' c
              refine ⟨n',d',item',?_,ra,rb⟩
              have t0 : tickNatural program (state heap next a b c d stack source 0) =
                  some ⟨state heap next a b c d stack source 1,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,hb,tagBranch]
              have t1 : tickNatural program (state heap next a b c d stack source 1) =
                  some ⟨state heap next tail b c d stack source 2,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,Registers.set,ht]
              have t2 : tickNatural program (state heap next tail b c d stack source 2) =
                  some ⟨state heap next tail btail c d stack source 0,[],0⟩ := by
                simp [tickNatural,program,state,Registers.get,Registers.set,hb]
              simpa [Nat.mul_add,Nat.add_assoc] using
                NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t2 run))

theorem read_high {i : ℕ} {rows : List (Bits × Bits)} (initial : NaturalState 7)
    (pc0 : initial.pc = 0) (table : Table initial.heap initial.registers.a rows)
    (index : IndexSpine initial.heap initial.registers.b i) (hi : i < rows.length) :
    ∃ final, NaturalRun program (3*i+4) initial [] final ∧
      BoolList final.heap final.registers.a rows[i].1 ∧
      BoolList final.heap final.registers.b rows[i].2 ∧
      final.heap=initial.heap ∧ final.next=initial.next ∧ final.stack=initial.stack ∧
      final.source=initial.source ∧ final.pc=6 ∧ tickNatural program final=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at pc0 table index
          subst pc
          obtain ⟨num,den,item,run,ra,rb⟩ := read table index hi next c d stack source
          exact ⟨state heap next num den item d stack source 6,run,ra,rb,
            rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The low interpreter pays both payload-reference copies and the final halt.
The representation theorem preserves the selected words without imposing any
canonical-bit or positivity condition on either incoming word. -/
theorem read_bit {i H B : ℕ} {rows : List (Bits × Bits)} (initial : BitState 7)
    (bounded : initial.Bounded H B) (pc0 : initial.pc = 0)
    (table : Table (eraseState initial).heap (eraseState initial).registers.a rows)
    (index : IndexSpine (eraseState initial).heap (eraseState initial).registers.b i)
    (hi : i < rows.length) :
    ∃ charge out, Run program (3*i+4) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a rows[i].1 ∧
      BoolList (eraseState out).heap (eraseState out).registers.b rows[i].2 ∧
      (eraseState out).heap=(eraseState initial).heap ∧ out.source=initial.source ∧ out.pc=6 ∧
      out.Bounded (H+(3*i+4)) (B+(3*i+4)) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 7 H B (3*i+4) := by
  obtain ⟨final,high,ra,rb,heap,_,_,src,pc,halt⟩ :=
    read_high (eraseState initial) pc0 table index hi
  obtain ⟨charge,out,run,erase,bound,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,?_,source.trans src,?_,bound,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase]; exact ra
  · rw [erase]; exact rb
  · rw [erase]; exact heap
  · exact (congrArg State.pc erase).trans pc

end DirectedFlowCutGap.WordPairTableRead
