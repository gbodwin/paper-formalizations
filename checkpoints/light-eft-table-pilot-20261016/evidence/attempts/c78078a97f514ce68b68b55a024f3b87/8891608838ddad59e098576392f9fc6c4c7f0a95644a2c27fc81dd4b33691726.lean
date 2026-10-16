import LightEFTSpanners.StoredOriginalWeightRows

namespace LightEFTSpanners.StoredOriginalWeightMatrix
open Controller

theorem reverse_trace (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) (xs out : StoredRecords.Weights) :
    Trace (transition n bank) (xs.length+1) (.reverse xs out) (.halt (xs.reverse++out)) := by
  induction xs generalizing out with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n bank (.reverse (x::xs) out)=some (.reverse xs (x::out)) from rfl) (ih (x::out))

def bound (n m : ℕ) : ℕ := n*rowBound n m+n+2

def execute (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) : StoredRecords.Weights :=
  match Controller.run (transition n bank) (bound n bank.length) (.rows 0 n []) with
  | .halt W => W
  | _ => []

theorem full_trace (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) :
    ∃ k, k ≤ bound n bank.length ∧ Trace (transition n bank) k (.rows 0 n []) (.halt (rows bank n 0 n)) := by
  obtain ⟨k,hk,ht⟩ := rows_trace n bank 0 n []
  simp only [List.append_nil] at ht
  have hr := reverse_trace n bank (rows bank n 0 n).reverse []
  simp only [List.reverse_reverse,List.length_reverse,rows_length,List.append_nil] at hr
  exact ⟨k+(n+1),by unfold bound;omega,ht.trans hr⟩

theorem execute_eq (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) : execute n bank=rows bank n 0 n := by
  obtain ⟨k,hk,ht⟩ := full_trace n bank
  have he : bound n bank.length=k+(bound n bank.length-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredOriginalWeightMatrix
