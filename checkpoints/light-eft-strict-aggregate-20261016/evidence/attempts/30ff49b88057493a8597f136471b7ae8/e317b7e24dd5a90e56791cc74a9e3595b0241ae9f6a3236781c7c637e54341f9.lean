import LightEFTSpanners.ExecutableVoting
import LightEFTSpanners.RationalDistanceWork
import LightEFTSpanners.FreshVotingTapes

/-! Literal instrumented empirical loops. The work field counts rational
arithmetic, table/oracle accesses and finite-set loop operations in the stated
unit-cost model. It is not a bit-cost theorem or a cost claim for constructing
the seed, hosts, order or random tape. Host identities are executable Fin J. -/
namespace LightEFTSpanners.ExecutableVoting
open SimpleGraph LightSpanners RationalDistance Finset
variable {n j : ℕ}

def distanceBudget (n : ℕ) : ℕ := 6*n^3+2*n^2+n+2

def sampleWork (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) :
    List (Finset (Sym2 (Fin n))) → ℕ × ℕ
  | [] => (0,1)
  | S::ss => let z := coveredWork (sampled Q E T S) w hw t e
             let r := sampleWork Q E T w hw t e ss
             (r.1+(if z.1 then 0 else 1),r.2+z.2+2)

 theorem sampleWork_value (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) (l : List (Finset (Sym2 (Fin n)))) :
    (sampleWork Q E T w hw t e l).1=
      (l.filter fun S => !(coveredTest (sampled Q E T S) w hw t e)).length := by
  induction l with
  | nil => rfl
  | cons S ss ih =>
    simp only [sampleWork, (coveredWork_spec _ w hw t e).1,ih]
    cases h : coveredTest (sampled Q E T S) w hw t e <;> simp [h,Nat.add_comm]

 theorem sampleWork_cost (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) (l : List (Finset (Sym2 (Fin n)))) :
    (sampleWork Q E T w hw t e l).2=1+l.length*(distanceBudget n+2) := by
  induction l with
  | nil => simp [sampleWork]
  | cons S ss ih =>
    simp only [sampleWork,(coveredWork_spec _ w hw t e).2,ih,List.length_cons,distanceBudget]
    ring

 def hostWork (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : List (Fin j) → Finset (Fin j) × ℕ
  | [] => (∅,1)
  | i::is => let r := hostWork Q w hw t eligible host tape E e is
             if i∈eligible e then
               let z := sampleWork Q E (host i) w hw t e (tape E e i)
               (if (3:ℚ)/8≤(z.1:ℚ)/(tape E e i).length then insert i r.1 else r.1,r.2+z.2+4)
             else (r.1,r.2+1)

 theorem hostWork_value (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (l : List (Fin j)) :
    (hostWork Q w hw t eligible host tape E e l).1=
      l.toFinset ∩ votes Q w hw t eligible host tape E e := by
  induction l with
  | nil => simp [hostWork]
  | cons i is ih =>
    by_cases he : i∈eligible e
    · simp only [hostWork,he,ite_true,sampleWork_value,ih]
      change (if (3:ℚ)/8≤estimate Q E (host i) w hw t e (tape E e i)
        then insert i (is.toFinset∩votes Q w hw t eligible host tape E e)
        else is.toFinset∩votes Q w hw t eligible host tape E e)=_
      split_ifs with hv
      · ext z
        simp only [List.toFinset_cons,Finset.mem_insert,Finset.mem_inter,votes,Finset.mem_filter]
        aesop
      · ext z
        simp only [List.toFinset_cons,Finset.mem_insert,Finset.mem_inter,votes,Finset.mem_filter]
        constructor
        · intro hz;exact ⟨Or.inr hz.1,hz.2⟩
        · rintro ⟨hz,hzv⟩
          rcases hz with rfl | hz
          · exact (hv hzv.2).elim
          · exact ⟨hz,hzv⟩

    · simp only [hostWork,he,ite_false,ih]
      ext z
      simp [votes]
      aesop

 theorem hostWork_cost_le (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (l : List (Fin j))
    (m : ℕ) (hm : ∀ i∈l,i∈eligible e → (tape E e i).length≤m) :
    (hostWork Q w hw t eligible host tape E e l).2≤
      1+l.length*(m*(distanceBudget n+2)+5) := by
  induction l with
  | nil => simp [hostWork]
  | cons i is ih =>
    have hi := ih (fun z hz => hm z (List.mem_cons_of_mem i hz))
    by_cases he : i∈eligible e
    · have hh := Nat.mul_le_mul_right (distanceBudget n+2) (hm i (by simp) he)
      simp only [hostWork,he,ite_true,sampleWork_cost,List.length_cons]
      nlinarith
    · simp only [hostWork,he,ite_false,List.length_cons]
      nlinarith

 def edgesWork (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (h : ℕ) : List (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) × ℕ
  | [] => (Q,1)
  | e::es => let r := edgesWork Q w hw t eligible host tape h es
             let z := hostWork Q w hw t eligible host tape r.1 e (List.finRange j)
             (if h≤z.1.card then insert e r.1 else r.1,r.2+z.2+3)

 theorem edgesWork_value (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (h : ℕ) (l : List (Sym2 (Fin n))) :
    (edgesWork Q w hw t eligible host tape h l).1=edges Q w hw t eligible host tape h l := by
  induction l with
  | nil => rfl
  | cons e es ih => simp [edgesWork,hostWork_value,ih,edges]

 theorem edgesWork_cost_le (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (h : ℕ) (l : List (Sym2 (Fin n))) (m : ℕ)
    (hm : ∀ E e i,(tape E e i).length≤m) :
    (edgesWork Q w hw t eligible host tape h l).2≤
      1+l.length*(j*(m*(distanceBudget n+2)+5)+4) := by
  induction l with
  | nil => simp [edgesWork]
  | cons e es ih =>
    have hh := hostWork_cost_le Q w hw t eligible host tape
      (edgesWork Q w hw t eligible host tape h es).1 e (List.finRange j) m
      (fun i _ _ => hm _ _ i)
    simp only [List.length_finRange] at hh
    simp only [edgesWork,List.length_cons]
    nlinarith

/-- The measured program has exactly the existing empirical output, together
with its explicit loop budget. Accuracy is not assumed for this equality. -/
 theorem measured_run_spec (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (h : ℕ) (l : List (Sym2 (Fin n))) (m : ℕ)
    (hm : ∀ E e i,(tape E e i).length≤m) :
    (edgesWork Q w hw t eligible host tape h l).1=
      SampledGreedy.edges Q (fun e => (w e:ℝ)) (t:ℝ) eligible host tape h l ∧
    (edgesWork Q w hw t eligible host tape h l).2≤
      1+l.length*(j*(m*(distanceBudget n+2)+5)+4) :=
  ⟨(edgesWork_value Q w hw t eligible host tape h l).trans
      (edges_eq Q w hw t eligible host tape h l),
    edgesWork_cost_le Q w hw t eligible host tape h l m hm⟩

/-- The actual finite assignment tapes have exactly m entries, so their
execution budget requires no supplied accuracy or sample-length assumption. -/
 theorem assignment_run_spec (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (m : ℕ)
    (a : SampledGreedy.Assignment (Fin n) (Fin j) m)
    (h : ℕ) (l : List (Sym2 (Fin n))) :
    (edgesWork Q w hw t eligible host (SampledGreedy.assignmentTape a) h l).1=
      SampledGreedy.edges Q (fun e => (w e:ℝ)) (t:ℝ) eligible host
        (SampledGreedy.assignmentTape a) h l ∧
    (edgesWork Q w hw t eligible host (SampledGreedy.assignmentTape a) h l).2≤
      1+l.length*(j*(m*(distanceBudget n+2)+5)+4) := by
  apply measured_run_spec
  intro E e i
  simp [SampledGreedy.assignmentTape]
end LightEFTSpanners.ExecutableVoting
