import DirectedFlowCutGap.ActualOracleChoice

/-! Actual demand discovery, stable selection and literal choice construction
are called inside one finite instruction table. -/
namespace DirectedFlowCutGap.GraphOracleMachine
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def demandLabel (pc : Fin 1604) : Fin 2120 := ⟨pc.val,by omega⟩
def choiceLabel (pc : Fin 484) : Fin 2120 := ⟨pc.val+1604,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 2120) : Instruction C → Instruction 2120
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 2120) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 2120 := fun pc =>
  if h : pc.val<1604 then callable demandLabel (DemandCollection.program ⟨pc.val,h⟩)
  else if h : pc.val<2088 then
    callable choiceLabel (OracleChoice.program ⟨pc.val-1604,by omega⟩)
  else match pc.val with
  | 2100 => .make .r2 (.pair .r0 .r1) 2101
  | 2101 => .field .r1 .r1 false 2102
  | 2102 => .call 1600 2103 .r3
  | 2103 => .field .r1 .r2 true 2104
  | 2104 => .field .r1 .r1 true 2105
  | 2105 => .move .r0 .r3 2106
  | 2106 => .call 2084 2107 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 2120)) (source : Bits) (pc : Fin 2120) : NaturalState 2120 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem demand_slots (pc : Fin 1604) (h : DemandCollection.program pc≠.halt) :
    program (demandLabel pc)=ReferenceProgramLabels.instruction demandLabel (DemandCollection.program pc) := by
  simpa [program,demandLabel,pc.isLt] using callable_eq demandLabel (DemandCollection.program pc) h
theorem demand_halt (pc : Fin 1604) (h : DemandCollection.program pc=.halt) :
    program (demandLabel pc)=.ret .r3 := by simp [program,demandLabel,h,pc.isLt,callable]
theorem choice_slots (pc : Fin 484) (h : OracleChoice.program pc≠.halt) :
    program (choiceLabel pc)=ReferenceProgramLabels.instruction choiceLabel (OracleChoice.program pc) := by
  simpa [program,choiceLabel,show ¬pc.val+1604<1604 by omega,show pc.val+1604<2088 by omega] using
    callable_eq choiceLabel (OracleChoice.program pc) h
theorem choice_halt (pc : Fin 484) (h : OracleChoice.program pc=.halt) :
    program (choiceLabel pc)=.ret .r3 := by
  simp [program,choiceLabel,show ¬pc.val+1604<1604 by omega,show pc.val+1604<2088 by omega,h,callable]

theorem run_append {s u v : NaturalState 2120} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

end DirectedFlowCutGap.GraphOracleMachine
