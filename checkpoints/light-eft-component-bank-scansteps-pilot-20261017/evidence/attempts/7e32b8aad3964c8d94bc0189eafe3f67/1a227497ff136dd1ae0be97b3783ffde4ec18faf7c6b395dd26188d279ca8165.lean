import LightEFTSpanners.SampleMatrixMachine

/-! Exact materialization traces, including both levels of reversal. -/
namespace LightEFTSpanners.SampleRecords
open LinkedDistance Controller
 def cellCount (R : Records) : ℕ := (R.map List.length).sum
 theorem rows_trace (i : ℕ) (R : Records) (out : Matrix) :
    Trace transition (2*cellCount R+3*R.length) (.row i R out)
      (.row (i+R.length) [] ((values i R).reverse++out)) := by
  induction R generalizing i out with
  | nil => simpa [cellCount,values] using Trace.refl (step:=transition) (.row i [] out)
  | cons r rs ih =>
    have h₀ := Trace.one (show transition (.row i (r::rs) out)=some (.cell i 0 r [] rs out) from rfl)
    have h₁ := cell_trace i 0 r [] rs out
    have h₂ := reverse_row_trace i rs out (rowValues i 0 r).reverse []
    simp only [List.append_nil] at h₁
    simp only [List.length_reverse,rowValues_length,List.reverse_reverse,List.append_nil] at h₂
    have h₃ := ih (i+1) (rowValues i 0 r::out)
    have h := h₀.trans (h₁.trans (h₂.trans h₃))
    convert h using 1 <;> simp [cellCount,values,List.reverse_cons,List.append_assoc] <;> omega
 theorem materialize_trace (R : Records) :
    Trace transition (2*cellCount R+4*R.length+2) (.row 0 R []) (.halt (values 0 R)) := by
  have h₁ := rows_trace 0 R []
  simp only [zero_add,List.append_nil] at h₁
  have h₂ := Trace.one (show transition (.row R.length [] (values 0 R).reverse)=
    some (.revMatrix (values 0 R).reverse []) from rfl)
  have h₃ := reverse_matrix_trace (values 0 R).reverse []
  simp only [List.length_reverse,values_length,List.reverse_reverse,List.append_nil] at h₃
  convert h₁.trans (h₂.trans h₃) using 1; omega
 theorem rowValues_ofFn {n : ℕ} (i j : ℕ) (f : Fin n → Entry) :
    rowValues i j (List.ofFn f)=List.ofFn (fun v => value i (j+v.val) (f v)) := by
  induction n generalizing j with
  | zero => simp [rowValues]
  | succ n ih =>
    simp only [List.ofFn_succ,rowValues,ih]
    congr 2
    funext v
    congr 1; simp [Nat.add_comm,Nat.add_left_comm]
 theorem values_ofFn {n : ℕ} (i : ℕ) (f : Fin n → List Entry) :
    values i (List.ofFn f)=List.ofFn (fun u => rowValues (i+u.val) 0 (f u)) := by
  induction n generalizing i with
  | zero => simp [values]
  | succ n ih =>
    simp only [List.ofFn_succ,values,ih]
    congr 2
    funext u
    congr 1; simp [Nat.add_comm,Nat.add_left_comm]
 theorem encode_cellCount {n : ℕ} (Q E T S : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ) :
    cellCount (encode Q E T S w)=n*n := by
  simp [cellCount,encode,List.map_ofFn,Function.comp_def]
 theorem encode_values {n : ℕ} (Q E T S : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ) :
    values 0 (encode Q E T S w)=matrixOf (ExecutableVoting.sampled Q E T S) w := by
  simp only [encode,values_ofFn,rowValues_ofFn,zero_add,matrixOf]
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  by_cases he : u=v
  · subst v;simp [value,ExecutableVoting.sampled,ExecutableVoting.graph,LightSpanners.edgeGraph]
  · have hv : u.val≠v.val := fun h => he (Fin.ext h)
    simp [value,hv,ExecutableVoting.sampled,ExecutableVoting.graph,LightSpanners.edgeGraph,he,and_assoc]
end LightEFTSpanners.SampleRecords
