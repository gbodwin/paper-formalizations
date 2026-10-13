import DirectedFlowCutGap.CanonicalRationalAddition
import DirectedFlowCutGap.CanonicalRationalSum

/-! Actual ordered traversal adds the same stored scalar to every original row
entry. Every rational addition, list cell and call frame is executed. -/
namespace DirectedFlowCutGap.ScalarAdditionRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def label (pc : Fin 142) : Fin 160 := ⟨pc.val,by omega⟩
def program : Program 160 := fun pc =>
  if pc.val=141 then .ret .r3
  else if h : pc.val<142 then
    ReferenceProgramLabels.instruction label (CanonicalRationalAddition.program ⟨pc.val,h⟩)
  else match pc.val with
  | 142 => .branch .r0 143 159 159 145
  | 143 => .make .r3 .nil 144
  | 144 => .ret .r3
  | 145 => .field .r2 .r0 false 146
  | 146 => .field .r0 .r0 true 147
  | 147 => .call 142 148 .r3
  | 148 => .move .r0 .r2 149
  | 149 => .move .r2 .r3 150
  | 150 => .call 140 151 .r3
  | 151 => .make .r3 (.pair .r3 .r2) 152
  | 152 => .ret .r3
  | 158 => .call 142 159 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 160)) (source : Bits) (pc : Fin 160) : NaturalState 160 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩
def result (scalar : Fraction) (xs : List Fraction) : List Fraction :=
  xs.map fun x => (BinaryRational.add x scalar).1

def steps (scalar : Fraction) : List Fraction → ℕ
  | [] => 3
  | x::xs => steps scalar xs + CanonicalRationalAddition.instructions x scalar + 11

def cells (scalar : Fraction) : List Fraction → ℕ
  | [] => 1
  | x::xs => cells scalar xs + CanonicalRationalAddition.cells x scalar + 1

theorem slots (pc : Fin 142) (h : CanonicalRationalAddition.program pc ≠ .halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (CanonicalRationalAddition.program pc) := by
  by_cases hp : pc.val=141
  · have he : pc=141 := Fin.ext hp
    subst pc;simp [CanonicalRationalAddition.program] at h
  · simp [program,label,pc.isLt,hp]

theorem run_append {s u v : NaturalState 160} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)
end DirectedFlowCutGap.ScalarAdditionRow
