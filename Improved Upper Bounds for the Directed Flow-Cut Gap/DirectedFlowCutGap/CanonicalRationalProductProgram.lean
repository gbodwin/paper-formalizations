import DirectedFlowCutGap.CanonicalArithmeticProgram
import DirectedFlowCutGap.RationalComparisonProgram

/-! Actual canonical rational multiplication for the outer packing objective
and update rows. Two concrete calls retain both original records. -/
namespace DirectedFlowCutGap.CanonicalRationalProduct
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def label (pc : Fin 116) : Fin 132 := ⟨pc.val,by omega⟩
def program : Program 132 := fun pc =>
  if pc.val=115 then .ret .r3
  else if h : pc.val<116 then
    ReferenceProgramLabels.instruction label (CanonicalArithmeticProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 116 => .make .r2 (.pair .r0 .r1) 117
  | 117 => .field .r0 .r0 false 118
  | 118 => .field .r1 .r1 false 119
  | 119 => .call 110 120 .r3
  | 120 => .make .r2 (.pair .r3 .r2) 121
  | 121 => .field .r0 .r2 true 122
  | 122 => .field .r1 .r0 true 123
  | 123 => .field .r0 .r0 false 124
  | 124 => .field .r0 .r0 true 125
  | 125 => .field .r1 .r1 true 126
  | 126 => .call 110 127 .r3
  | 127 => .field .r0 .r2 false 128
  | 128 => .make .r3 (.pair .r0 .r3) 129
  | 129 => .ret .r3
  | 130 => .call 116 131 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 132)) (source : Bits) (pc : Fin 132) : NaturalState 132 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩
def arithmeticCells (multiply : Bool) (xs ys : Bits) : ℕ :=
  CanonicalArithmeticProgram.rawCells multiply xs ys+
    (CanonicalArithmeticProgram.result multiply xs ys).length
def instructions (x y : BinaryRational.Fraction) : ℕ :=
  CanonicalArithmeticProgram.instructions true x.num y.num+
  CanonicalArithmeticProgram.instructions true x.den y.den+16
def cells (x y : BinaryRational.Fraction) : ℕ :=
  arithmeticCells true x.num y.num+arithmeticCells true x.den y.den+3

theorem slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc ≠ .halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (CanonicalArithmeticProgram.program pc) := by
  by_cases hp : pc.val=115
  · have he : pc=115 := Fin.ext hp
    subst pc;simp [CanonicalArithmeticProgram.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 132} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The actual canonical table is called with the original live caller stack. -/
theorem arithmetic_return (multiply : Bool) {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 132)
    (stack : List (Frame ℕ 132)) (source : Bits) :
    ∃ ext root, ext.length=arithmeticCells multiply xs ys ∧
      NaturalRun program (CanonicalArithmeticProgram.instructions multiply xs ys+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source
          (label (CanonicalArithmeticProgram.top multiply))) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root
        (if multiply then mulCanonical xs ys else addCanonical xs ys).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalArithmeticProgram.canonical_high multiply
    (CanonicalArithmeticProgram.state heap next a b c d [] source (CanonicalArithmeticProgram.top multiply))
    rfl hn left right rfl
  have lift := ReferenceProgramLabels.run label CanonicalArithmeticProgram.program program slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (CanonicalArithmeticProgram.instructions multiply xs ys)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source
        (label (CanonicalArithmeticProgram.top multiply))) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 115) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalArithmeticProgram.state,label,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 115)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,?_⟩
  · exact run_append body (.step ret (.done _))
  · rw [CanonicalArithmeticProgram.result_exact] at rep
    exact rep


end DirectedFlowCutGap.CanonicalRationalProduct
