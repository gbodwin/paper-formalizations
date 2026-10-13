import LightEFTSpanners.StoredFlagSample

namespace LightEFTSpanners.StoredFlagSample
open Controller

def bound (xs : Input) : ℕ := 2*xs.length+2

theorem full_trace (xs : Input) : ∃ k,k≤bound xs ∧
    Trace transition k (.scan xs []) (.halt (value xs)) := by
  have a := scan_trace xs []
  have b := reverse_trace (value xs).reverse []
  simp only [List.append_nil] at a
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at b
  have len := value_length xs
  refine ⟨(xs.length+1)+((value xs).length+1),?_,?_⟩
  · unfold bound;omega
  · exact a.trans b

def execute (xs : Input) : List StoredEdges.Edge :=
  match Controller.run transition (bound xs) (.scan xs []) with | .halt es => es | _ => []

theorem execute_eq (xs : Input) : execute xs=value xs := by
  obtain ⟨k,hk,ht⟩ := full_trace xs
  have he : bound xs=k+(bound xs-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]

theorem value_map {α : Type*} (xs : List α) (edge : α → StoredEdges.Edge) (bits : α → Bool) :
    value (xs.map fun x => (edge x,bits x))=(xs.filter bits).map edge := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hb : bits x <;> simp [value,hb,ih]
end LightEFTSpanners.StoredFlagSample
