import DirectedFlowCutGap.DemandSelectionRefinement

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem stored_record_of_mem {heap : NaturalHeap} {root : ℕ} {zs : List Record}
    (stored : RecordList heap root zs) {z : Record} (mem : z∈zs) : StoredRecord heap z := by
  induction stored with
  | nil _ => cases mem
  | cons _ hz _ ih =>
    rcases List.mem_cons.mp mem with rfl|mem
    · exact hz
    · exact ih mem

def GraphSelected {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits) :
    Option (BinaryFractionalGraphOracle.Selected n) → Prop
  | none => heap[root]?=some .nil
  | some q => ∃ z : Record,root=z.item.address ∧ StoredRecord heap z ∧ EncodesRecord label z q

theorem selected_payload {n : ℕ} {heap : NaturalHeap} {root listRoot : ℕ}
    {zs : List Record} {q : Option (BinaryFractionalGraphOracle.Selected n)} (label : Fin n → Bits)
    (stored : RecordList heap listRoot zs)
    (selected : RetainedArgminProgram.Selected heap root (RetainedArgminProgram.select (zs.map Record.item)))
    (related : OptionRelated (fun z q => z∈zs ∧ EncodesRecord label z q)
      (BinaryFractionalGraphOracle.argmin recordScore zs).1 q) : GraphSelected heap root label q := by
  rw [items_select] at selected
  cases ha : (BinaryFractionalGraphOracle.argmin recordScore zs).1 with
  | none =>
    cases q with
    | none => simpa only [ha,Option.map_none,RetainedArgminProgram.Selected,GraphSelected] using selected
    | some q => simp [ha,OptionRelated] at related
  | some z =>
    cases q with
    | none => simp [ha,OptionRelated] at related
    | some q =>
      have hr : z∈zs ∧ EncodesRecord label z q := by simpa only [ha,OptionRelated] using related
      have hs : RetainedArgminProgram.StoredItem heap root z.item := by simpa only [ha,Option.map_some,RetainedArgminProgram.Selected] using selected
      exact ⟨z,hs.1,stored_record_of_mem stored hr.1,hr.2⟩

end DirectedFlowCutGap.DemandCollection
