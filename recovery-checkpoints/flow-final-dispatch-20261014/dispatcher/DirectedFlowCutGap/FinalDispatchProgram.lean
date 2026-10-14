import DirectedFlowCutGap.GridFamilyEnvelope
import DirectedFlowCutGap.OriginalDispatchExecution

/-! NEW reconstruction from the published 722-source checkpoint. This file is
not recovered historical source and has no inherited compilation receipt. -/
namespace DirectedFlowCutGap.FinalDispatch
set_option maxRecDepth 32768
open BinaryArithmetic ImmutableReferenceSimulation

-- The disjoint child ranges preserve the already checked child bodies.
def gridLabel (pc : Fin 10760) : Fin 13320 := ⟨pc.val,by omega⟩
def dispatchLabel (pc : Fin 2140) : Fin 13320 := ⟨10760+pc.val,by omega⟩
def vertexLabel (pc : Fin 44) : Fin 13320 := ⟨12900+pc.val,by omega⟩
def minimumLabel (pc : Fin 320) : Fin 13320 := ⟨12944+pc.val,by omega⟩

def callable {C : ℕ} (label : Fin C → Fin 13320) : Instruction C → Instruction 13320
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

/-- The controller matches only small relative labels. The entry receives the
original cost, matrix and demand roots in a/b/c and returns its output in d. -/
def program : Program 13320 := fun pc =>
  if h : pc.val<10760 then callable gridLabel (GridFamilyInput.program ⟨pc.val,h⟩)
  else if h : pc.val<12900 then callable dispatchLabel (OriginalDispatch.program ⟨pc.val-10760,by omega⟩)
  else if h : pc.val<12944 then callable vertexLabel (RowVertices.program ⟨pc.val-12900,by omega⟩)
  else if h : pc.val<13264 then callable minimumLabel (OriginalRowMinimum.program ⟨pc.val-12944,by omega⟩)
  else match pc.val-13264 with
  | 6 => .call 12940 13271 .r3
  | 7 => .make .r1 (.pair .r0 .r1) 13272
  | 8 => .make .r1 (.pair .r3 .r1) 13273
  | 9 => .move .r0 .r2 13274
  | 10 => .call 12898 13275 .r3
  | 11 => .ret .r3
  | 36 => .call 13270 13301 .r3
  | 37 => .make .r2 (.pair .r2 .r3) 13302
  | 38 => .field .r3 .r3 false 13303
  | 39 => .branch .r3 13306 13304 13304 13319
  | 40 => .field .r3 .r2 true 13305
  | 41 => .ret .r3
  | 42 => .field .r2 .r2 false 13307
  | 43 => .call 13262 13308 .r3
  | 44 => .branch .r3 13305 13319 13319 13309
  | 45 => .call 10758 13310 .r3
  | 46 => .make .r0 .nil 13311
  | 47 => .make .r3 (.pair .r0 .r3) 13305
  | 54 => .call 13300 13319 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 13320)) (source : Bits) (pc : Fin 13320) : NaturalState 13320 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem callable_eq {C : ℕ} (label : Fin C → Fin 13320) (op : Instruction C) (h : op≠.halt) :
    callable label op=ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

theorem grid_slots (pc : Fin 10760) (h : GridFamilyInput.program pc≠.halt) :
    program (gridLabel pc)=ReferenceProgramLabels.instruction gridLabel (GridFamilyInput.program pc) := by
  simpa [program,gridLabel,pc.isLt] using callable_eq gridLabel (GridFamilyInput.program pc) h

theorem dispatch_slots (pc : Fin 2140) (h : OriginalDispatch.program pc≠.halt) :
    program (dispatchLabel pc)=ReferenceProgramLabels.instruction dispatchLabel (OriginalDispatch.program pc) := by
  simpa [program,dispatchLabel,show ¬10760+pc.val<10760 by omega,
    show 10760+pc.val<12900 by omega] using callable_eq dispatchLabel (OriginalDispatch.program pc) h

theorem vertex_slots (pc : Fin 44) (h : RowVertices.program pc≠.halt) :
    program (vertexLabel pc)=ReferenceProgramLabels.instruction vertexLabel (RowVertices.program pc) := by
  simpa [program,vertexLabel,show ¬12900+pc.val<10760 by omega,
    show ¬12900+pc.val<12900 by omega,show 12900+pc.val<12944 by omega] using
    callable_eq vertexLabel (RowVertices.program pc) h

theorem minimum_slots (pc : Fin 320) (h : OriginalRowMinimum.program pc≠.halt) :
    program (minimumLabel pc)=ReferenceProgramLabels.instruction minimumLabel (OriginalRowMinimum.program pc) := by
  simpa [program,minimumLabel,show ¬12944+pc.val<10760 by omega,
    show ¬12944+pc.val<12900 by omega,show ¬12944+pc.val<12944 by omega,
    show 12944+pc.val<13264 by omega] using
    callable_eq minimumLabel (OriginalRowMinimum.program pc) h
end DirectedFlowCutGap.FinalDispatch
