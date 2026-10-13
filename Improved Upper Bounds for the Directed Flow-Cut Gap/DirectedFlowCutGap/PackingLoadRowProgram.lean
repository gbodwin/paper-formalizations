import DirectedFlowCutGap.PackingLoadEntryExecution

namespace DirectedFlowCutGap.PackingLoadRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

def label (pc : Fin 160) : Fin 200 := ⟨pc.val,by omega⟩
def callable : Instruction 160 → Instruction 200
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 200 := fun pc =>
  if h : pc.val<160 then callable (PackingLoadEntry.program ⟨pc.val,h⟩)
  else match pc.val with
  | 160 => .branch .r0 161 191 191 163
  | 161 => .make .r3 .nil 162
  | 162 => .ret .r3
  | 163 => .make .r3 (.pair .r0 .r1) 164
  | 164 => .field .r2 .r1 false 165
  | 165 => .field .r2 .r2 false 166
  | 166 => .field .r1 .r1 true 167
  | 167 => .field .r0 .r0 false 168
  | 168 => .call 142 169 .r0
  | 169 => .make .r3 (.pair .r0 .r3) 170
  | 170 => .field .r2 .r3 true 171
  | 171 => .field .r1 .r2 true 172
  | 172 => .field .r0 .r1 false 173
  | 173 => .field .r0 .r0 true 174
  | 174 => .field .r1 .r1 true 175
  | 175 => .make .r1 (.pair .r0 .r1) 176
  | 176 => .field .r0 .r2 false 177
  | 177 => .field .r0 .r0 true 178
  | 178 => .call 160 179 .r0
  | 179 => .field .r1 .r3 false 180
  | 180 => .make .r3 (.pair .r1 .r0) 181
  | 181 => .ret .r3
  | 190 => .call 160 191 .r0
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 200)) (source : Bits) (pc : Fin 200) : NaturalState 200 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def result (amount : Fraction) : List Fraction → List Bool → List Fraction
  | y::ys,f::fs => PackingLoadEntry.result f amount y::result amount ys fs
  | _,_ => []

def steps (amount : Fraction) : List Fraction → List Bool → ℕ
  | y::ys,f::fs => PackingLoadEntry.steps f amount y+steps amount ys fs+21
  | _,_ => 3

def cells (amount : Fraction) : List Fraction → List Bool → ℕ
  | y::ys,f::fs => PackingLoadEntry.cells f amount y+cells amount ys fs+4
  | _,_ => 1

theorem slots (pc : Fin 160) (h : PackingLoadEntry.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (PackingLoadEntry.program pc) := by
  have he : callable (PackingLoadEntry.program pc)=ReferenceProgramLabels.instruction label (PackingLoadEntry.program pc) := by
    cases hh : PackingLoadEntry.program pc <;> simp_all [callable]
  simpa [program,label,pc.isLt] using he

theorem run_append {s u v : NaturalState 200} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)
end DirectedFlowCutGap.PackingLoadRow
