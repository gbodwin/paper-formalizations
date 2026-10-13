import DirectedFlowCutGap.PackingGraphContext

namespace DirectedFlowCutGap.PackingAmount
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def label (pc : Fin 30) : Fin 44 := ⟨pc.val,by omega⟩
def callable (pc : Fin 30) : Instruction 44 :=
  if IndexedRationalRead.program pc=.halt then .ret .r3
  else ReferenceProgramLabels.instruction label (IndexedRationalRead.program pc)

def program : Program 44 := fun pc =>
  if h : pc.val<30 then callable ⟨pc.val,h⟩ else match pc.val with
  | 40 => .field .r0 .r0 true 41
  | 41 => .call 28 42 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 44)) (source : Bits) (pc : Fin 44) : NaturalState 44 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem slots (pc : Fin 30) (h : IndexedRationalRead.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (IndexedRationalRead.program pc) := by
  simp [program,label,pc.isLt,callable,h]

theorem read_return {word : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (index : BoolList heap a word) (table : StoredList heap b rows)
    (hi : value word<rows.length) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 44) (stack : List (Frame ℕ 44)) (source : Bits) :
    ∃ ext root,ext.length=value word+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps word+4)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 28) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (IndexedRationalRead.lookup rows word) := by
  obtain ⟨ext,root,len,core,rep⟩ := IndexedRationalRead.read_high
    (IndexedRationalRead.state heap next a b c d [] source 28) rfl hn rfl index
    (PackingGraphContext.row_table table) hi
  have body := ReferenceProgramLabels.run label IndexedRationalRead.program program slots core
  have body := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) body
  have lifted : NaturalRun program (BinaryIndexedPairRead.steps word+3)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 28) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 29) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramStack.state,IndexedRationalRead.state,label,state] using body
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 29)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,callable,IndexedRationalRead.program,state,Registers.get,Registers.set]
  have tail := NaturalRun.step ret (NaturalRun.done _)
  have append {s u v : NaturalState 44} {t k : ℕ} {events more : List Event}
      (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
      NaturalRun program (t+k) s (events++more) v := by
    induction h with
    | done s => simpa using g
    | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
        using NaturalRun.step ht (ih g)
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using append lifted tail,rep⟩
end DirectedFlowCutGap.PackingAmount
