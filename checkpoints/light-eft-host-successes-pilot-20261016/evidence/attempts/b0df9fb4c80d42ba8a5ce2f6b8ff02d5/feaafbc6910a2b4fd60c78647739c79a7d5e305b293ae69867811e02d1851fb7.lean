import LightEFTSpanners.StoredOriginalWeightMatrix

namespace LightEFTSpanners.StoredOriginalWeightMatrix
open Controller

theorem lookup_lift (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) (i j l k : ℕ)
    (row : List ℚ) (acc : StoredRecords.Weights) {steps : ℕ} {s u : StoredOriginalWeightLookup.State}
    (h : Trace (StoredOriginalWeightLookup.transition (i,j)) steps s u) :
    Trace (transition n bank) steps (.lookup i j l k row acc s) (.lookup i j l k row acc u) := by
  induction h with
  | refl => exact .refl _
  | @cons steps s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredOriginalWeightLookup.transition] at he
    | scan rs => simpa only [transition,Option.map_some] using congrArg (Option.map (State.lookup i j l k row acc)) he

theorem cells_trace (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) (i j l k : ℕ)
    (r : List ℚ) (acc : StoredRecords.Weights) :
    ∃ steps, steps ≤ l*(bank.length+3)+1 ∧ Trace (transition n bank) steps
      (.cells i j l k r acc) (.reverseRow i k ((row bank i j l).reverse++r) [] acc) := by
  induction l generalizing j r with
  | zero => exact ⟨1,by simp,Trace.one rfl⟩
  | succ l ih =>
    have a := Trace.one (show transition n bank (.cells i j (l+1) k r acc)=
      some (.lookup i j l k r acc (.scan bank)) from rfl)
    have b := lookup_lift n bank i j l k r acc (StoredOriginalWeightLookup.lookup_trace (i,j) bank)
    have c := Trace.one (show transition n bank (.lookup i j l k r acc
      (.halt (StoredOriginalWeightLookup.value (i,j) bank)))=
      some (.cells i (j+1) l k (StoredOriginalWeightLookup.value (i,j) bank::r) acc) from rfl)
    obtain ⟨steps,hs,ht⟩ := ih (j+1) (StoredOriginalWeightLookup.value (i,j) bank::r)
    have hb := StoredOriginalWeightLookup.steps_le (i,j) bank
    refine ⟨1+StoredOriginalWeightLookup.steps (i,j) bank+1+steps,by nlinarith,?_⟩
    simpa [row,List.reverse_cons,List.append_assoc,Nat.add_assoc] using a.trans (b.trans (c.trans ht))

theorem reverse_row (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) (i k : ℕ)
    (xs out : List ℚ) (acc : StoredRecords.Weights) :
    Trace (transition n bank) (xs.length+1) (.reverseRow i k xs out acc)
      (.rows (i+1) k ((xs.reverse++out)::acc)) := by
  induction xs generalizing out with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n bank (.reverseRow i k (x::xs) out acc)=
        some (.reverseRow i k xs (x::out) acc) from rfl) (ih (x::out))

def rowBound (n m : ℕ) : ℕ := n*(m+3)+n+3

theorem rows_trace (n : ℕ) (bank : StoredOriginalWeightLookup.Bank) (i k : ℕ)
    (acc : StoredRecords.Weights) :
    ∃ steps, steps ≤ k*rowBound n bank.length+1 ∧ Trace (transition n bank) steps
      (.rows i k acc) (.reverse ((rows bank n i k).reverse++acc) []) := by
  induction k generalizing i acc with
  | zero => exact ⟨1,by simp,Trace.one rfl⟩
  | succ k ih =>
    have a := Trace.one (show transition n bank (.rows i (k+1) acc)=some (.cells i 0 n k [] acc) from rfl)
    obtain ⟨steps,hs,ht⟩ := cells_trace n bank i 0 n k [] acc
    simp only [List.append_nil] at ht
    have b := reverse_row n bank i k (row bank i 0 n).reverse [] acc
    simp only [List.reverse_reverse,List.append_nil,List.length_reverse,row_length] at b
    obtain ⟨l,hl,hu⟩ := ih (i+1) (row bank i 0 n::acc)
    refine ⟨1+steps+(n+1)+l,?_,?_⟩
    · unfold rowBound at *;nlinarith
    · simpa [rows,List.reverse_cons,List.append_assoc,Nat.add_assoc] using a.trans (ht.trans (b.trans hu))
end LightEFTSpanners.StoredOriginalWeightMatrix
