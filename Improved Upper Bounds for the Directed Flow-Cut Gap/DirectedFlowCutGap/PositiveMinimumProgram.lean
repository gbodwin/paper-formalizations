import DirectedFlowCutGap.PositiveInventoryRefinement

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic ImmutableReferenceSimulation

def inventoryLabel (pc : Fin 48) : Fin 256 := ⟨pc.val,by omega⟩
def argminLabel (pc : Fin 194) : Fin 256 := ⟨pc.val+48,by omega⟩
def callable {C : ℕ} (label : Fin C → Fin 256) : Instruction C → Instruction 256
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

def program : Program 256 := fun pc =>
  if h : pc.val<48 then callable inventoryLabel (PositiveInventory.program ⟨pc.val,h⟩)
  else if h : pc.val<242 then callable argminLabel (RetainedArgminProgram.program ⟨pc.val-48,by omega⟩)
  else match pc.val with
  | 248 => .call 46 249 .r3
  | 249 => .move .r0 .r3 250
  | 250 => .call 226 251 .r3
  | 251 => .ret .r3
  | 254 => .call 248 255 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 256)) (source : Bits) (pc : Fin 256) : NaturalState 256 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem inventory_slots (pc : Fin 48) (h : PositiveInventory.program pc≠.halt) :
    program (inventoryLabel pc)=ReferenceProgramLabels.instruction inventoryLabel (PositiveInventory.program pc) := by
  simp only [program,inventoryLabel,show pc.val<48 from pc.isLt,↓reduceDIte]
  generalize he : PositiveInventory.program pc=op at *
  cases op <;> simp_all [callable]

theorem argmin_slots (pc : Fin 194) (h : RetainedArgminProgram.program pc≠.halt) :
    program (argminLabel pc)=ReferenceProgramLabels.instruction argminLabel (RetainedArgminProgram.program pc) := by
  have h1 : ¬pc.val+48<48 := by omega
  have h2 : pc.val+48<242 := by omega
  simp only [program,argminLabel,h1,h2,↓reduceDIte,Nat.add_sub_cancel]
  generalize he : RetainedArgminProgram.program pc=op at *
  cases op <;> simp_all [callable]
end DirectedFlowCutGap.PositiveMinimum
