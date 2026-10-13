import DirectedFlowCutGap.PositiveMinimumProgram

namespace DirectedFlowCutGap.PositiveMinimum
open ImmutableReferenceSimulation

theorem run_append {s u v : NaturalState 256} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- A literal existing submachine trace is relocated into the adaptive program,
with the real caller frame and one paid return instruction. -/
theorem child_return {C : ℕ} (label : Fin C → Fin 256) (child : Program C)
    (slots : ∀ pc,child pc≠.halt → program (label pc)=ReferenceProgramLabels.instruction label (child pc))
    {k : ℕ} {s t : NaturalState C} {events : List Event}
    (core : NaturalRun child k s events t) (hs : s.stack=[]) (ht : t.stack=[])
    (result destination : Reg) (saved : Registers ℕ) (pc : Fin 256)
    (stack : List (Frame ℕ 256)) (terminal : program (label t.pc)=.ret result) :
    NaturalRun program (k+1)
      (state s.heap s.next s.registers.a s.registers.b s.registers.c s.registers.d
        (⟨pc,destination,saved⟩::stack) s.source (label s.pc)) events
      ⟨t.heap,t.next,saved.set destination (t.registers.get result),stack,pc,t.source⟩ := by
  have h := ReferenceProgramLabels.run label child program slots core
  have h := ReferenceProgramStack.run program (⟨pc,destination,saved⟩::stack) h
  have body : NaturalRun program k
      (state s.heap s.next s.registers.a s.registers.b s.registers.c s.registers.d
        (⟨pc,destination,saved⟩::stack) s.source (label s.pc)) events
      (state t.heap t.next t.registers.a t.registers.b t.registers.c t.registers.d
        (⟨pc,destination,saved⟩::stack) t.source (label t.pc)) := by
    cases s with
    | mk sh sn sr ss sp sx =>
      cases t with
      | mk th tn tr ts tp tx =>
        simp only at hs ht
        subst ss;subst ts
        cases sr;cases tr
        simpa [ReferenceProgramLabels.state,ReferenceProgramStack.state,state] using h
  have ret : tickNatural program
      (state t.heap t.next t.registers.a t.registers.b t.registers.c t.registers.d
        (⟨pc,destination,saved⟩::stack) t.source (label t.pc))=
      some ⟨⟨t.heap,t.next,saved.set destination (t.registers.get result),stack,pc,t.source⟩,[],0⟩ := by
    cases t.registers
    simp [tickNatural,state,terminal]
  simpa using run_append body (.step ret (.done _))
end DirectedFlowCutGap.PositiveMinimum
