import DirectedFlowCutGap.ActualRationalQuotient
import DirectedFlowCutGap.CanonicalRationalSum

/-! A stored row is traversed and divided by a stored scalar, or a scalar is
 divided by every original row entry. Both modes call the actual quotient table. -/
namespace DirectedFlowCutGap.ScalarQuotientRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def label (pc : Fin 164) : Fin 182 := ⟨pc.val,by omega⟩
def program (scalarNumerator : Bool) : Program 182 := fun pc =>
  if pc.val=162 then .ret .r3
  else if h : pc.val<164 then
    ReferenceProgramLabels.instruction label (CanonicalRationalQuotient.program ⟨pc.val,h⟩)
  else match pc.val with
  | 164 => .branch .r0 165 181 181 167
  | 165 => .make .r3 .nil 166
  | 166 => .ret .r3
  | 167 => .field .r2 .r0 false 168
  | 168 => .field .r0 .r0 true 169
  | 169 => .call 164 170 .r3
  | 170 => .move .r0 .r2 171
  | 171 => .move .r2 .r3 172
  | 172 => if scalarNumerator then .move .r3 .r0 173 else .call 161 176 .r3
  | 173 => .move .r0 .r1 174
  | 174 => .move .r1 .r3 175
  | 175 => .call 161 176 .r3
  | 176 => .make .r3 (.pair .r3 .r2) 177
  | 177 => .ret .r3
  | 180 => .call 164 181 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 182)) (source : Bits) (pc : Fin 182) : NaturalState 182 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def numerator (mode : Bool) (scalar x : Fraction) : Fraction := if mode then scalar else x
def denominator (mode : Bool) (scalar x : Fraction) : Fraction := if mode then x else scalar
def result (mode : Bool) (scalar : Fraction) (xs : List Fraction) : List Fraction :=
  xs.map fun x => (BinaryRational.div (numerator mode scalar x) (denominator mode scalar x)).1

def steps (mode : Bool) (scalar : Fraction) : List Fraction → ℕ
  | [] => 3
  | x::xs => steps mode scalar xs +
      CanonicalRationalQuotient.steps (numerator mode scalar x) (denominator mode scalar x) +
      (if mode then 14 else 11)
def cells (mode : Bool) (scalar : Fraction) : List Fraction → ℕ
  | [] => 1
  | x::xs => cells mode scalar xs +
      CanonicalRationalQuotient.cells (numerator mode scalar x) (denominator mode scalar x) + 1

theorem slots (mode : Bool) (pc : Fin 164) (h : CanonicalRationalQuotient.program pc ≠ .halt) :
    program mode (label pc)=ReferenceProgramLabels.instruction label (CanonicalRationalQuotient.program pc) := by
  by_cases hp : pc.val=162
  · have he : pc=162 := Fin.ext hp
    subst pc;simp [CanonicalRationalQuotient.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append (mode : Bool) {s u v : NaturalState 182} {t k : ℕ} {events more : List Event}
    (h : NaturalRun (program mode) t s events u) (g : NaturalRun (program mode) k u more v) :
    NaturalRun (program mode) (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem quotient_return (mode : Bool) (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 182)
    (stack : List (Frame ℕ 182)) (source : Bits) :
    ∃ ext root, ext.length=CanonicalRationalQuotient.cells x y ∧
      NaturalRun (program mode) (CanonicalRationalQuotient.steps x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 161) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.div x y).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalQuotient.quotient_high x y
    (CanonicalRationalQuotient.state heap next a b c d [] source 161) rfl hn left right rfl
  have lift := ReferenceProgramLabels.run label CanonicalRationalQuotient.program (program mode) (slots mode) core
  have lift := ReferenceProgramStack.run (program mode) (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun (program mode) (1+CanonicalRationalQuotient.steps x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 161) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 162) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalQuotient.state,label,state] using lift
  have ret : tickNatural (program mode)
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 162)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append mode body (.step ret (.done _)) using 1 <;> simp
  omega
end DirectedFlowCutGap.ScalarQuotientRow
