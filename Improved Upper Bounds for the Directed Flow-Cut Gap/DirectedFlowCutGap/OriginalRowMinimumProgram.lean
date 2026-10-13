import DirectedFlowCutGap.OriginalMinimumPositive
import DirectedFlowCutGap.ActualRowVertices
import DirectedFlowCutGap.ScalarAdditionRowEncoding

namespace DirectedFlowCutGap.OriginalRowMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def vertexLabel (pc : Fin 44) : Fin 320 := ⟨pc.val,by omega⟩
def minimumLabel (pc : Fin 256) : Fin 320 := ⟨44+pc.val,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 320) : Instruction C → Instruction 320
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

theorem callable_eq {C : ℕ} (label : Fin C → Fin 320) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 320 := fun pc =>
  if h : pc.val<44 then callable vertexLabel (RowVertices.program ⟨pc.val,h⟩)
  else if h : pc.val<300 then callable minimumLabel (PositiveMinimum.program ⟨pc.val-44,by omega⟩)
  else match pc.val with
  | 300 => .call 40 301 .r3
  | 301 => .move .r1 .r0 302
  | 302 => .move .r0 .r3 303
  | 303 => .call 298 304 .r3
  | 304 => .ret .r3
  | 318 => .call 300 319 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 320)) (source : Bits) (pc : Fin 320) : NaturalState 320 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem vertex_slots (pc : Fin 44) (h : RowVertices.program pc≠.halt) :
    program (vertexLabel pc)=ReferenceProgramLabels.instruction vertexLabel (RowVertices.program pc) := by
  simpa [program,vertexLabel,pc.isLt] using callable_eq vertexLabel (RowVertices.program pc) h

theorem minimum_slots (pc : Fin 256) (h : PositiveMinimum.program pc≠.halt) :
    program (minimumLabel pc)=ReferenceProgramLabels.instruction minimumLabel (PositiveMinimum.program pc) := by
  simpa [program,minimumLabel,show ¬44+pc.val<44 by omega,show 44+pc.val<300 by omega] using
    callable_eq minimumLabel (PositiveMinimum.program pc) h

def result (rows : List Fraction) : Option (Bits × Fraction) :=
  PositiveMinimum.select (PositiveInventory.selected ((RowVertexScan.words rows.length []).zip rows))

def inputSteps (rows : List Fraction) : ℕ :=
  RowVertices.instructionBound rows.length+
  PositiveMinimum.inputSteps rows (SourceRowTableProgram.bits (IndexedRationalRead.fields rows))+8
end DirectedFlowCutGap.OriginalRowMinimum
