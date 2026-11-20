import DirectedFlowCutGap.BinaryAllocationTrace

/-! Materialize a returned row or mask with the certified array constructors. -/
namespace DirectedFlowCutGap.TerminalArrayAssembly

open BinaryArithmetic EncodedArrayStorage
open EncodedRoundingInput (collect collect_value)

def entries {A : Type} (values : List A) : List (A × ℕ) := values.map fun value => (value, 0)

def run {A : Type} (values : List A) : Array A := (collect (entries values)).1

@[simp] theorem value {A : Type} (values : List A) : run values = values.toArray := by
  apply Array.toList_inj.mp
  unfold run
  rw [collect_value]
  simp [entries, List.map_map, Function.comp_def]

def vector {A : Type} {n : ℕ} (values : List A) (width : values.length = n) : Vector A n :=
  ⟨run values, by rw [value,List.size_toArray,width]⟩

@[simp] theorem vector_value {A : Type} {n : ℕ} (values : List A) (width : values.length = n) :
    vector values width = ⟨values.toArray, by simpa using width⟩ := by
  apply Vector.toArray_inj.mp
  exact value values

def schedule {A : Type} (values : List A) : List (Instruction A) := collectTrace (entries values)

theorem execution {A : Type} (values : List A) :
    CollectExec (entries values) (run values) (schedule values) := collect_exec (entries values)

theorem space {A : Type} (values : List A) :
    (schedule values).length = 2*values.length^2+21*values.length+4 ∧
      fresh (schedule values) ≤ values.length^2+7*values.length+2 := by
  constructor
  · simpa only [schedule,entries,List.length_map] using collectTrace_length (entries values)
  · rw [schedule,collectTrace_fresh]
    simpa only [entries,List.length_map] using collectCells_bound values.length

theorem address_width {A : Type} (values : List A) (start : ℕ) (block : ℕ × ℕ)
    (inTrace : block ∈ (allocateTrace start (schedule values)).2) (offset : ℕ) (valid : offset < block.2) :
    (block.1+offset).size ≤ (start+(values.length^2+7*values.length+2)).size := by
  apply Nat.size_le_size
  exact (allocated_address (schedule values) start block inTrace offset valid).2.le.trans
    (Nat.add_le_add_left (space values).2 start)

end DirectedFlowCutGap.TerminalArrayAssembly
