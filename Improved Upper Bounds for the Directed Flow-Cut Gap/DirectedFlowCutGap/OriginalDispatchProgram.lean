import DirectedFlowCutGap.ActualAvoidingDemandScan

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

inductive Value where
  | infeasible (demand : Bits × Bits)
  | zero (mask : Bits)
  | positive (witness : (Bits × Bits) × GraphWalkExtension.Walk)

def Result (heap : NaturalHeap) (p : ℕ) : Value → Prop
  | .infeasible e => ∃ tag out,heap[p]?=some (.pair tag out) ∧
      heap[tag]?=some (.flag false) ∧ EmptyDemandEdge.Demand heap out e.1 e.2
  | .zero mask => ∃ tag out,heap[p]?=some (.pair tag out) ∧
      heap[tag]?=some (.flag true) ∧ BoolList heap out mask
  | .positive e => ∃ tag out,heap[p]?=some (.pair tag out) ∧
      heap[tag]?=some .nil ∧ AvoidingDemandScan.Result heap out (some e)

abbrev Context := AvoidingDemandScan.Context
abbrev Table := AvoidingDemandScan.Table

def emptyLabel (pc : Fin 160) : Fin 2140 := ⟨pc.val,by omega⟩
def zeroLabel (pc : Fin 32) : Fin 2140 := ⟨160+pc.val,by omega⟩
def scanLabel (pc : Fin 1900) : Fin 2140 := ⟨192+pc.val,by omega⟩

def program : Program 2140 := fun pc =>
  if pc.val=159 then .ret .r3
  else if h : pc.val<160 then
    ReferenceProgramLabels.instruction emptyLabel (EmptyDemandScan.program ⟨pc.val,h⟩)
  else if pc.val=191 then .ret .r3
  else if h : pc.val<192 then
    ReferenceProgramLabels.instruction zeroLabel (PackingZeroMask.program ⟨pc.val-160,by omega⟩)
  else if pc.val=2091 then .ret .r3
  else if h : pc.val<2092 then
    ReferenceProgramLabels.instruction scanLabel (AvoidingDemandScan.program ⟨pc.val-192,by omega⟩)
  else match pc.val with
  | 2110 => .make .r2 (.pair .r0 .r1) 2111
  | 2111 => .field .r1 .r1 true 2112
  | 2112 => .field .r1 .r1 true 2113
  | 2113 => .call 158 2114 .r3
  | 2114 => .branch .r3 2120 2139 2139 2115
  | 2115 => .make .r0 (.flag false) 2116
  | 2116 => .make .r3 (.pair .r0 .r3) 2117
  | 2117 => .ret .r3
  | 2120 => .field .r1 .r2 true 2121
  | 2121 => .call 2090 2122 .r3
  | 2122 => .branch .r3 2125 2139 2139 2123
  | 2123 => .make .r0 .nil 2124
  | 2124 => .make .r3 (.pair .r0 .r3) 2117
  | 2125 => .field .r0 .r1 true 2126
  | 2126 => .field .r0 .r0 false 2127
  | 2127 => .call 190 2128 .r3
  | 2128 => .make .r0 (.flag true) 2129
  | 2129 => .make .r3 (.pair .r0 .r3) 2117
  | 2138 => .call 2110 2139 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 2140)) (source : Bits) (pc : Fin 2140) : NaturalState 2140 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem empty_slots (pc : Fin 160) (h : EmptyDemandScan.program pc≠.halt) :
    program (emptyLabel pc)=ReferenceProgramLabels.instruction emptyLabel (EmptyDemandScan.program pc) := by
  by_cases hp : pc.val=159
  · have he : pc=159 := Fin.ext hp
    subst pc;simp [EmptyDemandScan.program] at h
  · simp [program,emptyLabel,pc.isLt,hp]

theorem zero_slots (pc : Fin 32) (h : PackingZeroMask.program pc≠.halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (PackingZeroMask.program pc) := by
  by_cases hp : pc.val=31
  · have he : pc=31 := Fin.ext hp
    subst pc;simp [PackingZeroMask.program] at h
  · have ha : 160+pc.val≠191 := by omega
    simp [program,zeroLabel,ha,show ¬160+pc.val=159 by omega,
      show ¬160+pc.val<160 by omega,show 160+pc.val<192 by omega]

theorem scan_slots (pc : Fin 1900) (h : AvoidingDemandScan.program pc≠.halt) :
    program (scanLabel pc)=ReferenceProgramLabels.instruction scanLabel (AvoidingDemandScan.program pc) := by
  by_cases hp : pc.val=1899
  · have he : pc=1899 := Fin.ext hp
    subst pc;simp [AvoidingDemandScan.program] at h
  · have ha : 192+pc.val≠2091 := by omega
    simp [program,scanLabel,ha,show ¬192+pc.val=159 by omega,
      show ¬192+pc.val<160 by omega,show ¬192+pc.val=191 by omega,
      show ¬192+pc.val<192 by omega,show 192+pc.val<2092 by omega]
end DirectedFlowCutGap.OriginalDispatch
