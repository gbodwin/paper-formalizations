import DirectedFlowCutGap.ReferenceProgramLabels
import DirectedFlowCutGap.ReferenceProgramStack
import DirectedFlowCutGap.ConcreteExpressionProgram

/-! Call a relocated program and return through the saved physical frame. -/

namespace DirectedFlowCutGap.ReferenceProgramInvocation

open ImmutableReferenceSimulation

def state {P : ℕ} (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ P))
    (tape : List Bool) (pc : Fin P) : NaturalState P := ⟨heap,heap.length,r,stack,pc,tape⟩

theorem call {C D work : ℕ} {small : Program C} {large : Program D}
    (label : Fin C→Fin D)
    (agree : ∀ pc,small pc≠.halt → large (label pc)=ReferenceProgramLabels.instruction label (small pc))
    {start finish : Fin C} {caller continuation : Fin D} {result : Reg} {dst : Reg}
    (enter : large caller=.call (label start) continuation dst)
    (exit : large (label finish)=.ret result)
    {heap ext : NaturalHeap} {r out : Registers ℕ} {tape suffix : List Bool} {events : List Event}
    (stack : List (Frame ℕ D))
    (body : NaturalRun small work (state heap r [] tape start) events (state (heap++ext) out [] suffix finish)) :
    NaturalRun large (work+2) (state heap r stack tape caller) events
      (state (heap++ext) (r.set dst (out.get result)) stack suffix continuation) := by
  let frame : Frame ℕ D := ⟨continuation,dst,r⟩
  have startStep : tickNatural large (state heap r stack tape caller)=
      some ⟨state heap r (frame::stack) tape (label start),[],0⟩ := by
    simp [state,tickNatural,enter,frame]
  have stopStep : tickNatural large (state (heap++ext) out (frame::stack) suffix (label finish))=
      some ⟨state (heap++ext) (r.set dst (out.get result)) stack suffix continuation,[],0⟩ := by
    simp [state,tickNatural,exit,frame]
  have lifted := ReferenceProgramLabels.run label small large agree body
  have lifted := ReferenceProgramStack.run large (frame::stack) lifted
  have trace : NaturalRun large work (state heap r (frame::stack) tape (label start)) events
      (state (heap++ext) out (frame::stack) suffix (label finish)) := lifted
  have tail := ConcreteExpressionProgram.append_run trace (NaturalRun.step stopStep (.done _))
  simpa only [List.nil_append,List.append_nil,Nat.zero_add,Nat.add_assoc] using NaturalRun.step startStep tail

end DirectedFlowCutGap.ReferenceProgramInvocation
