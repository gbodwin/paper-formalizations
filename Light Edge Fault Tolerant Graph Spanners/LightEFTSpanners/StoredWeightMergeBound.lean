import LightEFTSpanners.StoredWeightMergeTrace

namespace LightEFTSpanners.StoredWeightMerge
open Controller

theorem work_le (bank : StoredOriginalWeightLookup.Bank) (xs ys : List StoredEdges.Edge) :
    work bank xs ys≤(xs.length+ys.length)*(2*bank.length+8)+2 := by
  induction xs generalizing ys with
  | nil => simp only [work_nil_left,List.length_nil,Nat.zero_add];nlinarith
  | cons x xs ih =>
    induction ys with
    | nil => simp only [work_nil_right,List.length_nil,Nat.add_zero,List.length_cons];nlinarith
    | cons y ys iy =>
      have hc := StoredWeightComparison.steps_le bank x y
      have hx := ih (y::ys)
      simp only [work_cons_cons,List.length_cons] at hx iy ⊢
      split <;> nlinarith

def bound (bank : StoredOriginalWeightLookup.Bank) (xs ys : List StoredEdges.Edge) : ℕ :=
  (xs.length+ys.length)*(2*bank.length+9)+3

theorem full_trace (bank : StoredOriginalWeightLookup.Bank) (xs ys : List StoredEdges.Edge) :
    ∃ k,k≤bound bank xs ys ∧ Trace (transition bank) k (.merge xs ys [])
      (.halt (List.merge xs ys (StoredWeightComparison.result bank))) := by
  let out := List.merge xs ys (StoredWeightComparison.result bank)
  have a := merge_trace bank xs ys []
  simp only [List.append_nil] at a
  have z := reverse_trace bank out.reverse []
  simp only [List.reverse_reverse,List.append_nil] at z
  refine ⟨work bank xs ys+(out.reverse.length+1),?_,a.trans z⟩
  have h := work_le bank xs ys
  have hl : out.length=xs.length+ys.length := List.length_merge (StoredWeightComparison.result bank) xs ys
  simp only [List.length_reverse]
  unfold bound
  nlinarith

def execute (bank : StoredOriginalWeightLookup.Bank) (xs ys : List StoredEdges.Edge) : List StoredEdges.Edge :=
  match Controller.run (transition bank) (bound bank xs ys) (.merge xs ys []) with
  | .halt out => out
  | _ => []

theorem execute_eq (bank : StoredOriginalWeightLookup.Bank) (xs ys : List StoredEdges.Edge) :
    execute bank xs ys=List.merge xs ys (StoredWeightComparison.result bank) := by
  obtain ⟨k,hk,ht⟩ := full_trace bank xs ys
  have he : bound bank xs ys=k+(bound bank xs ys-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredWeightMerge
