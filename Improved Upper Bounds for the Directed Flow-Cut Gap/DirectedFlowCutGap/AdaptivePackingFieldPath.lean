import DirectedFlowCutGap.AdaptivePackingCallLift

namespace DirectedFlowCutGap.AdaptivePackingState
open ImmutableReferenceSimulation

/-- A structural path through original immutable pair cells. -/
inductive HeapPath (heap : NaturalHeap) : ℕ → List Bool → ℕ → Prop
  | nil (root) : HeapPath heap root [] root
  | cons {root left right target side rest} : heap[root]?=some (.pair left right) →
      HeapPath heap (if side then right else left) rest target → HeapPath heap root (side::rest) target

/-- The actual statically fixed field instructions, including their continuations.
The empty suffix reads a register into itself. -/
inductive FieldSequence (destination : Reg) : Reg → Fin 4800 → List Bool → Fin 4800 → Prop
  | nil (pc) : FieldSequence destination destination pc [] pc
  | cons {source pc side next rest finish} : program pc=.field destination source side next →
      FieldSequence destination destination next rest finish →
      FieldSequence destination source pc (side::rest) finish

theorem field_sequence_run {destination source : Reg} {pc finish : Fin 4800} {sides : List Bool}
    (slots : FieldSequence destination source pc sides finish)
    {heap : NaturalHeap} {regs : Registers ℕ} {target : ℕ}
    (path : HeapPath heap (regs.get source) sides target)
    (next : ℕ) (stack : List (Frame ℕ 4800)) (input : List Bool) :
    NaturalRun program sides.length ⟨heap,next,regs,stack,pc,input⟩ []
      ⟨heap,next,regs.set destination target,stack,finish,input⟩ := by
  induction slots generalizing regs target with
  | nil pc =>
    cases path
    cases destination <;> cases regs <;> exact .done _
  | @cons source pc side nextPc rest finish slot tail ih =>
    cases path with
    | @cons root left right target side rest cell path =>
      have tick : tickNatural program ⟨heap,next,regs,stack,pc,input⟩=
          some ⟨⟨heap,next,regs.set destination (if side then right else left),stack,nextPc,input⟩,[],0⟩ := by
        simp [tickNatural,slot,cell]
      have hp : HeapPath heap ((regs.set destination (if side then right else left)).get destination) rest target := by
        cases destination <;> simpa [Registers.get,Registers.set] using path
      have h := NaturalRun.step tick (ih hp)
      cases destination <;> cases regs <;>
        simpa [Registers.get,Registers.set] using h

theorem path_extend {heap : NaturalHeap} {root target : ℕ} {sides : List Bool}
    (h : HeapPath heap root sides target) (ext : NaturalHeap) : HeapPath (heap++ext) root sides target := by
  induction h with
  | nil root => exact .nil root
  | cons hp _ ih => exact .cons (PackedBooleanConstructor.lookup_extend hp ext) ih

theorem path_append {heap : NaturalHeap} {root middle target : ℕ} {left right : List Bool}
    (a : HeapPath heap root left middle) (b : HeapPath heap middle right target) :
    HeapPath heap root (left++right) target := by
  induction a with
  | nil root => exact b
  | cons hp _ ih => exact .cons hp (ih b)
end DirectedFlowCutGap.AdaptivePackingState
