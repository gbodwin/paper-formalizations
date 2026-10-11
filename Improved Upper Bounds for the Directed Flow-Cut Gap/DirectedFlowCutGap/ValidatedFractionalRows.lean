import DirectedFlowCutGap.SourceRowAcceptanceProgram
import DirectedFlowCutGap.RowInputBudgets

/-! The accepting machine branch discharges the existing fractional-row input
interface. Only erased positivity certificates are added: every stored padded
numerator and denominator and the same heap table are retained. -/
namespace DirectedFlowCutGap.ValidatedFractionalRows
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal

def fromPositive (rows : List (Bits × Bits))
    (positive : ∀ p ∈ rows, 0 < value p.2) : Row rows.length :=
  Vector.ofFn fun i => ⟨rows[i].1,rows[i].2,positive _ (List.getElem_mem i.isLt)⟩

theorem fields_fromPositive (rows : List (Bits × Bits))
    (positive : ∀ p ∈ rows, 0 < value p.2) :
    RowInputBudgets.fields (fromPositive rows positive)=rows := by
  simp [RowInputBudgets.fields,fromPositive,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]

theorem fields_positive {n : ℕ} (row : Row n) :
    ∀ p ∈ RowInputBudgets.fields row, 0 < value p.2 := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  exact q.den_pos

theorem representable_iff (rows : List (Bits × Bits)) :
    (∃ row : Row rows.length, RowInputBudgets.fields row=rows) ↔
      ∀ p ∈ rows, 0 < value p.2 := by
  constructor
  · rintro ⟨row,eq⟩
    rw [← eq]
    exact fields_positive row
  · intro h
    exact ⟨fromPositive rows h,fields_fromPositive rows h⟩

/-- Acceptance supplies a fractional row with precisely the source fields;
rejection rules out every such row. Both facts concern the very same executed
table, unused suffix and terminal-inclusive operation charge. -/
theorem from_source (rows : List (Bits × Bits)) (suffix : Bits) :
    ∃ charge out, Run SourceRowAcceptanceProgram.program
        (SourceRowAcceptanceProgram.instructions rows) charge
        (SourceRowAcceptanceProgram.initial (SourceRowTableProgram.encode rows++suffix))
        ((SourceRowTableProgram.encode rows).map Event.request) out ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.a rows ∧
      (out.pc=58 ↔ ∃ row : Row rows.length, RowInputBudgets.fields row=rows) ∧
      (out.pc=58 → ∃ row : Row rows.length,
        RowInputBudgets.fields row=rows ∧
        WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.a (RowInputBudgets.fields row)) ∧
      out.source=suffix ∧ out.stack=[] ∧
      out.heap.length=SourceRowTableProgram.cells rows+(RowTableValidationProgram.flags rows).length ∧
      (attempt SourceRowAcceptanceProgram.program out).result=none ∧
      charge+(attempt SourceRowAcceptanceProgram.program out).operations ≤
        40000000*(SourceRowTableProgram.bits rows+rows.length+1)^3 := by
  obtain ⟨charge,out,run,table,_,accept,_,src,frames,len,halt,cost⟩ :=
    SourceRowAcceptanceProgram.accept_from_source rows suffix
  refine ⟨charge,out,run,table,accept.trans (representable_iff rows).symm,?_,src,frames,len,halt,
    cost.trans (SourceRowAcceptanceProgram.total_bound rows)⟩
  intro h
  obtain ⟨row,eq⟩ := (representable_iff rows).mpr (accept.mp h)
  exact ⟨row,eq,eq.symm ▸ table⟩

end DirectedFlowCutGap.ValidatedFractionalRows
