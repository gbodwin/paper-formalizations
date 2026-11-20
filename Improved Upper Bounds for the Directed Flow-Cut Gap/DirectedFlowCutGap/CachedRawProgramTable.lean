import DirectedFlowCutGap.RawGraphControllerProgram

/-! The cached raw controller uses a fixed finite instruction table.
Compilation of the table depends only on the original program. -/
namespace DirectedFlowCutGap.CachedRawProgramTable

open ImmutableReferenceSimulation
open RawGraphControllerProgram (program)

def code : Vector (Instruction 26704) 26704 := Vector.ofFn program

theorem code_size : code.toArray.size = 26704 := code.size_toArray

theorem in_bounds (pc : Fin 26704) : pc.val < code.toArray.size := by
  simpa only [code_size] using pc.isLt

attribute [local irreducible] code

def dispatch (pc : Fin 26704) : Instruction 26704 := code.get pc

theorem dispatch_eq : dispatch = program := by
  funext pc
  unfold dispatch code
  exact Vector.getElem_ofFn (f := program) pc.isLt

theorem label_width (pc : Fin 26704) : pc.val.size ≤ 15 :=
  Nat.size_le.mpr (pc.isLt.trans_le (by decide))

end DirectedFlowCutGap.CachedRawProgramTable
