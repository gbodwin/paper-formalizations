import LightEFTSpanners.LinkedDistanceInitialization

/-! The concrete list matrix is the literal encoding of the existing graph,
and its controller result is the already proved rational shortest-walk test. -/
namespace LightEFTSpanners.LinkedDistance
open RationalDistance

 theorem zipWith_ofFn {α β γ : Type*} {n : ℕ} (f : α → β → γ)
    (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b)=List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ,List.zipWith_cons_cons,ih]

 theorem rows_ofFn {n : ℕ} (d : List Cell) (a : Fin n → List Cell) (b : Fin n → Cell) :
    rows d (List.ofFn a) (List.ofFn b)=List.ofFn (fun i => scan (a i) d (b i)) := by
  induction n with
  | zero => simp [rows]
  | succ n ih => simp only [List.ofFn_succ,rows,ih]

 def encode {n : ℕ} (d : Vector Cell n) : List Cell := List.ofFn (fun i : Fin n => d[i.val])

 theorem scan_encoded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector Cell n) (u : Fin n) :
    scan (List.ofFn (fun v => if G.Adj u v then some (w s(u,v)) else none)) (encode d) d[u.val]=
      (step G w d)[u.val] := by
  rw [scan_eq_fold]
  unfold encode
  rw [zipWith_ofFn]
  have he : (fun v : Fin n => addCell (if G.Adj u v then some (w s(u,v)) else none) d[v.val])=
      candidate G w d u := by
    funext v
    by_cases h : G.Adj u v <;> cases hv : d[v.val] <;> simp [candidate,h,addCell,hv]
  rw [he]
  simp [step,List.finRange,List.map_ofFn,Function.comp_def]

 theorem rows_encoded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector Cell n) :
    rows (encode d) (matrixOf G w) (encode d)=encode (step G w d) := by
  unfold matrixOf encode
  rw [rows_ofFn]
  apply congrArg List.ofFn
  funext u
  exact scan_encoded G w d u

 theorem initial_encoded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (v : Fin n) :
    initial n v.val=encode (table G w v 0) := by
  apply List.ext_getElem
  · simp [initial,encode]
  · intro i h₁ h₂
    simp only [initial,List.getElem_map,List.getElem_range,encode,List.getElem_ofFn,table_zero,Vector.getElem_ofFn]
    simp [Fin.ext_iff]

 theorem rounds_encoded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (v : Fin n) (k m : ℕ) :
    rounds (matrixOf G w) k (encode (table G w v m))=encode (table G w v (m+k)) := by
  induction k generalizing m with
  | zero => simp [rounds]
  | succ k ih =>
    simp only [rounds,rows_encoded]
    change rounds (matrixOf G w) k (encode (table G w v (m+1)))=_
    rw [ih]
    congr 2
    omega

 theorem linked_table_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (v : Fin n) :
    rounds (matrixOf G w) n (initial n v.val)=encode (table G w v n) := by
  rw [initial_encoded G w v,rounds_encoded]
  simp

 theorem machine_shortTest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) :
    ∃ t,t≤n^3+3*n^2+6*n+4 ∧
      Executes (transition n (matrixOf G w) u.val v.val budget) t (.init n 0 [])
        (.halt (shortTest G w u v budget)) := by
  obtain ⟨t,ht,he⟩ := machine_terminates n (matrixOf G w) u.val v.val budget (by simp [matrixOf]) u.isLt
  refine ⟨t,ht,?_⟩
  simpa [linked_table_eq,encode,shortTest,List.getElem?_ofFn] using he

end LightEFTSpanners.LinkedDistance
