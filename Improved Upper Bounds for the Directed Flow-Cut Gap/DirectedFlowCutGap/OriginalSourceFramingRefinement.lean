import DirectedFlowCutGap.OriginalSourceFraming
import DirectedFlowCutGap.ChargedSourceTables

/-! The fixed framing interpreter agrees with the original source parser's
framing phase, including its literal source suffix. -/
namespace DirectedFlowCutGap.OriginalSourceFraming

open BinaryArithmetic ImmutableReferenceSimulation
open WordPairTableRead (Table)

theorem original_none (source : Bits) :
    (read source).1=none ↔ EncodedVertexInput.readTables source=none := by
  rw [read_none]
  constructor
  · intro rejected
    cases h : EncodedVertexInput.readTables source with
    | none => rfl
    | some fields =>
        obtain ⟨c,m,d,t⟩ := fields
        exact (rejected ⟨c,m,d,t,
          ChargedSourceTables.tables_wire ((ChargedSourceTables.tables_value source).trans h)⟩).elim
  · rintro rejected ⟨c,m,d,t,wire⟩
    simp only [wire,EncodedVertexInput.readTables_prefix,Option.some_ne_none] at rejected

theorem original_tables {source : Bits} {c m d : EncodedVertexInput.Table} {suffix : Bits}
    (parsed : EncodedVertexInput.readTables source=some (c,m,d,suffix)) :
    ∃ out, (read source).1=some out ∧ out.source=suffix ∧
      Table (eraseState out).heap (eraseState out).registers.a c ∧
      Table (eraseState out).heap (eraseState out).registers.b m ∧
      Table (eraseState out).heap (eraseState out).registers.d d ∧
      out.pc=51 ∧ out.stack=[] ∧ value out.next=out.heap.length :=
  read_correct (ChargedSourceTables.tables_wire ((ChargedSourceTables.tables_value source).trans parsed))

end DirectedFlowCutGap.OriginalSourceFraming
