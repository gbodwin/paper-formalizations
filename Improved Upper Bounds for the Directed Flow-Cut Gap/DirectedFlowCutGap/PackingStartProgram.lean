import DirectedFlowCutGap.PackingGraphContext
import DirectedFlowCutGap.PackingZeroRowConstruction
import DirectedFlowCutGap.ActualNormalizedRow
import DirectedFlowCutGap.ActualObjectiveRow

/-! A single finite controller constructs the initial packing state. All six
calls operate on their actual same-heap outputs; the only static context is the
original demand list, enumeration, adjacency and capacities. -/
namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def initialLabel (pc : Fin 182) : Fin 3060 := ⟨pc.val+0,by omega⟩
def contextLabel (pc : Fin 10) : Fin 3060 := ⟨pc.val+182,by omega⟩
def oracleLabel (pc : Fin 2120) : Fin 3060 := ⟨pc.val+192,by omega⟩
def normalizedLabel (pc : Fin 372) : Fin 3060 := ⟨pc.val+2312,by omega⟩
def objectiveLabel (pc : Fin 312) : Fin 3060 := ⟨pc.val+2684,by omega⟩
def zeroLabel (pc : Fin 16) : Fin 3060 := ⟨pc.val+2996,by omega⟩

def callable {C : ℕ} (label : Fin C → Fin 3060) : Instruction C → Instruction 3060
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 3060) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 3060 := fun pc =>
  if h : pc.val<182 then callable initialLabel ((ScalarQuotientRow.program true) ⟨pc.val-0,by omega⟩)
  else if h : pc.val<192 then callable contextLabel ((PackingGraphContext.program) ⟨pc.val-182,by omega⟩)
  else if h : pc.val<2312 then callable oracleLabel ((GraphOracleMachine.program) ⟨pc.val-192,by omega⟩)
  else if h : pc.val<2684 then callable normalizedLabel ((NormalizedRow.program) ⟨pc.val-2312,by omega⟩)
  else if h : pc.val<2996 then callable objectiveLabel ((ObjectiveRow.program) ⟨pc.val-2684,by omega⟩)
  else if h : pc.val<3012 then callable zeroLabel ((PackingZeroRow.program) ⟨pc.val-2996,by omega⟩)
  else match pc.val with
  | 3020 => .make .r2 (.pair .r0 .r2) 3021
  | 3021 => .call 180 3022 .r3
  | 3022 => .make .r2 (.pair .r3 .r2) 3023
  | 3023 => .move .r0 .r3 3024
  | 3024 => .field .r1 .r2 true 3025
  | 3025 => .field .r1 .r1 true 3026
  | 3026 => .field .r1 .r1 true 3027
  | 3027 => .call 190 3028 .r3
  | 3028 => .move .r1 .r3 3029
  | 3029 => .field .r0 .r2 true 3030
  | 3030 => .field .r0 .r0 true 3031
  | 3031 => .field .r0 .r0 false 3032
  | 3032 => .call 2292 3033 .r3
  | 3033 => .field .r1 .r3 false 3034
  | 3034 => .field .r0 .r2 false 3035
  | 3035 => .call 2676 3036 .r3
  | 3036 => .make .r2 (.pair .r3 .r2) 3037
  | 3037 => .move .r1 .r3 3038
  | 3038 => .field .r0 .r2 true 3039
  | 3039 => .field .r0 .r0 true 3040
  | 3040 => .field .r0 .r0 false 3041
  | 3041 => .call 2992 3042 .r3
  | 3042 => .make .r2 (.pair .r3 .r2) 3043
  | 3043 => .call 3004 3044 .r3
  | 3044 => .make .r0 .nil 3045
  | 3045 => .field .r1 .r3 true 3046
  | 3046 => .make .r1 (.pair .r1 .r0) 3047
  | 3047 => .field .r0 .r3 false 3048
  | 3048 => .make .r1 (.pair .r0 .r1) 3049
  | 3049 => .field .r0 .r2 false 3050
  | 3050 => .make .r1 (.pair .r0 .r1) 3051
  | 3051 => .field .r2 .r2 true 3052
  | 3052 => .field .r0 .r2 false 3053
  | 3053 => .make .r1 (.pair .r0 .r1) 3054
  | 3054 => .field .r2 .r2 true 3055
  | 3055 => .field .r0 .r2 false 3056
  | 3056 => .make .r3 (.pair .r0 .r1) 3057
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 3060)) (source : Bits) (pc : Fin 3060) : NaturalState 3060 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem initial_slots (pc : Fin 182) (h : (ScalarQuotientRow.program true) pc≠.halt) :
    program (initialLabel pc)=ReferenceProgramLabels.instruction initialLabel ((ScalarQuotientRow.program true) pc) := by
  simpa [program,initialLabel, show pc.val+0<182 by omega] using callable_eq initialLabel ((ScalarQuotientRow.program true) pc) h

theorem context_slots (pc : Fin 10) (h : (PackingGraphContext.program) pc≠.halt) :
    program (contextLabel pc)=ReferenceProgramLabels.instruction contextLabel ((PackingGraphContext.program) pc) := by
  simpa [program,contextLabel, show ¬pc.val+182<182 by omega, show pc.val+182<192 by omega] using callable_eq contextLabel ((PackingGraphContext.program) pc) h

theorem oracle_slots (pc : Fin 2120) (h : (GraphOracleMachine.program) pc≠.halt) :
    program (oracleLabel pc)=ReferenceProgramLabels.instruction oracleLabel ((GraphOracleMachine.program) pc) := by
  simpa [program,oracleLabel, show ¬pc.val+192<182 by omega, show ¬pc.val+192<192 by omega, show pc.val+192<2312 by omega] using callable_eq oracleLabel ((GraphOracleMachine.program) pc) h

theorem normalized_slots (pc : Fin 372) (h : (NormalizedRow.program) pc≠.halt) :
    program (normalizedLabel pc)=ReferenceProgramLabels.instruction normalizedLabel ((NormalizedRow.program) pc) := by
  simpa [program,normalizedLabel, show ¬pc.val+2312<182 by omega, show ¬pc.val+2312<192 by omega, show ¬pc.val+2312<2312 by omega, show pc.val+2312<2684 by omega] using callable_eq normalizedLabel ((NormalizedRow.program) pc) h

theorem objective_slots (pc : Fin 312) (h : (ObjectiveRow.program) pc≠.halt) :
    program (objectiveLabel pc)=ReferenceProgramLabels.instruction objectiveLabel ((ObjectiveRow.program) pc) := by
  simpa [program,objectiveLabel, show ¬pc.val+2684<182 by omega, show ¬pc.val+2684<192 by omega, show ¬pc.val+2684<2312 by omega, show ¬pc.val+2684<2684 by omega, show pc.val+2684<2996 by omega] using callable_eq objectiveLabel ((ObjectiveRow.program) pc) h

theorem zero_slots (pc : Fin 16) (h : (PackingZeroRow.program) pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel ((PackingZeroRow.program) pc) := by
  simpa [program,zeroLabel, show ¬pc.val+2996<182 by omega, show ¬pc.val+2996<192 by omega, show ¬pc.val+2996<2312 by omega, show ¬pc.val+2996<2684 by omega, show ¬pc.val+2996<2996 by omega, show pc.val+2996<3012 by omega] using callable_eq zeroLabel ((PackingZeroRow.program) pc) h

theorem run_append {s u v : NaturalState 3060} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)
end DirectedFlowCutGap.PackingStart
