import DirectedFlowCutGap.ActualCapacityBottleneck

/-! The selected record's original demand occurrence is recovered from the
actual allocated record list and the preserved initial demand list. -/
namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem records_original (vs adjacency : List Bits) (rows : List Fraction) (next : ℕ)
    (xs : List Demand) : ∀ z∈records vs adjacency rows next xs,z.demand∈xs := by
  induction xs with
  | nil => simp [records]
  | cons x xs ih =>
    intro z hz
    cases hq : query vs adjacency rows x with
    | none =>
      simp only [records,hq] at hz
      exact List.mem_cons_of_mem _ (ih z hz)
    | some q =>
      simp only [records,hq] at hz
      rcases List.mem_cons.mp hz with rfl|hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih z hz)

theorem demand_occurrence {heap : NaturalHeap} {root : ℕ} {xs : List Demand}
    (input : DemandList heap root xs) {x : Demand} (hx : x∈xs) :
    StoredDemand heap x ∧ ∃ tail,heap[x.occurrence]?=some (.pair x.record tail) := by
  induction input with
  | nil _ => cases hx
  | @cons p tail y ys he hp hy _ ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · exact ⟨hy,tail,by simpa [he] using hp⟩
    · exact ih hx

def SelectedOrigin {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits) :
    Option (BinaryFractionalGraphOracle.Selected n) → Prop
  | none => heap[root]?=some .nil
  | some q => ∃ z : Record,root=z.item.address ∧ StoredRecord heap z ∧
      EncodesRecord label z q ∧ StoredDemand heap z.demand ∧
      ∃ tail,heap[z.demand.occurrence]?=some (.pair z.demand.record tail)

theorem selected_origin {n : ℕ} {heap : NaturalHeap} {root listRoot demandRoot : ℕ}
    {xs : List Demand} {zs : List Record} {q : Option (BinaryFractionalGraphOracle.Selected n)}
    (label : Fin n → Bits) (stored : RecordList heap listRoot zs)
    (demands : DemandList heap demandRoot xs) (original : ∀ z∈zs,z.demand∈xs)
    (selected : RetainedArgminProgram.Selected heap root (RetainedArgminProgram.select (zs.map Record.item)))
    (related : OptionRelated (fun z q => z∈zs ∧ EncodesRecord label z q)
      (BinaryFractionalGraphOracle.argmin recordScore zs).1 q) : SelectedOrigin heap root label q := by
  rw [items_select] at selected
  cases ha : (BinaryFractionalGraphOracle.argmin recordScore zs).1 with
  | none =>
    cases q with
    | none => simpa only [ha,Option.map_none,RetainedArgminProgram.Selected,SelectedOrigin] using selected
    | some q => simp [ha,OptionRelated] at related
  | some z =>
    cases q with
    | none => simp [ha,OptionRelated] at related
    | some q =>
      have hr : z∈zs ∧ EncodesRecord label z q := by simpa only [ha,OptionRelated] using related
      have hs : RetainedArgminProgram.StoredItem heap root z.item := by
        simpa only [ha,Option.map_some,RetainedArgminProgram.Selected] using selected
      obtain ⟨hd,tail,hnode⟩ := demand_occurrence demands (original z hr.1)
      exact ⟨z,hs.1,stored_record_of_mem stored hr.1,hr.2,hd,tail,hnode⟩

end DirectedFlowCutGap.DemandCollection
