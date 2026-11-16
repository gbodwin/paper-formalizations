import LightEFTSpanners.CorrectedRuntimeWork

/-! Paid conditional loops for arbitrary finite supplied host identities.
The host enumeration is input data; its completeness is proved explicitly,
and all its iterations are charged. The sample assignments remain supplied
inputs rather than an uncharged random-generation primitive. This is the
same abstract unit-cost finite-set/table-access loop metric as
CorrectedRuntimeWork, rather than a concrete representation or bit-cost bound. -/
namespace LightEFTSpanners.CorrectedExecution
open SimpleGraph LightSpanners RationalDistance Finset CorrectedRuntime
variable {n : ℕ} {J : Type*} [DecidableEq J]
variable (hostIndices : List J)
 def hostWork (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : List (J) → Finset (J) × ℕ :=
  List.rec (∅,1) (fun i _ r =>
    if i∈eligible e then
      let z := sampleWork Q E (host i) w hw t e (tape E e i)
      (if (1:ℚ)/8≤(z.1:ℚ)/(tape E e i).length then insert i r.1 else r.1,r.2+z.2+4)
    else (r.1,r.2+1))

 theorem hostWork_nil (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    hostWork Q w hw t eligible host tape E e [] = (∅,1) := rfl

 theorem hostWork_cons (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (i : J) (is : List (J)) :
    hostWork Q w hw t eligible host tape E e (i :: is) =
      let r := hostWork Q w hw t eligible host tape E e is
      if i∈eligible e then
        let z := sampleWork Q E (host i) w hw t e (tape E e i)
        (if (1:ℚ)/8≤(z.1:ℚ)/(tape E e i).length then insert i r.1 else r.1,r.2+z.2+4)
      else (r.1,r.2+1) := rfl

 theorem hostWork_value (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (l : List (J)) :
    (hostWork Q w hw t eligible host tape E e l).1=
      l.toFinset ∩ votes Q w hw t eligible host tape E e := by
  induction l with
  | nil => simp [hostWork_nil]
  | cons i is ih =>
    by_cases he : i∈eligible e
    · simp only [hostWork_cons,he,ite_true,sampleWork_value,ih]
      change (if (1:ℚ)/8≤estimate Q E (host i) w hw t e (tape E e i)
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

    · simp only [hostWork_cons,he,ite_false,ih]
      ext z
      simp [votes]
      aesop

 theorem hostWork_cost_le (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (l : List (J))
    (m : ℕ) (hm : ∀ i∈l,i∈eligible e → (tape E e i).length≤m) :
    (hostWork Q w hw t eligible host tape E e l).2≤
      1+l.length*(m*(distanceBudget n+2)+5) := by
  induction l with
  | nil => simp [hostWork_nil]
  | cons i is ih =>
    have hi := ih (fun z hz => hm z (List.mem_cons_of_mem i hz))
    by_cases he : i∈eligible e
    · have hh := Nat.mul_le_mul_right (distanceBudget n+2) (hm i (by simp) he)
      simp only [hostWork_cons,he,ite_true,sampleWork_cost,List.length_cons]
      nlinarith
    · simp only [hostWork_cons,he,ite_false,List.length_cons]
      nlinarith

 def edgesWork (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (h : ℕ) : List (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) × ℕ :=
  List.rec (Q,1) (fun e _ r =>
    let z := hostWork Q w hw t eligible host tape r.1 e (hostIndices)
    (if h≤z.1.card then insert e r.1 else r.1,r.2+z.2+3))

 theorem edgesWork_nil (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (h : ℕ) :
    edgesWork hostIndices Q w hw t eligible host tape h [] = (Q,1) := rfl

 theorem edgesWork_cons (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (h : ℕ) (e : Sym2 (Fin n)) (es : List (Sym2 (Fin n))) :
    edgesWork hostIndices Q w hw t eligible host tape h (e :: es) =
      let r := edgesWork hostIndices Q w hw t eligible host tape h es
      let z := hostWork Q w hw t eligible host tape r.1 e (hostIndices)
      (if h≤z.1.card then insert e r.1 else r.1,r.2+z.2+3) := rfl

 theorem edgesWork_value [Fintype J] (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (h : ℕ) (l : List (Sym2 (Fin n))) (hIndices : hostIndices.toFinset = (univ : Finset J)) :
    (edgesWork hostIndices Q w hw t eligible host tape h l).1=edges Q w hw t eligible host tape h l := by
  induction l with
  | nil => rfl
  | cons e es ih => simp [edgesWork_cons,hostWork_value,ih,edges_cons,hIndices]

 theorem edgesWork_cost_le (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (h : ℕ) (l : List (Sym2 (Fin n))) (m : ℕ)
    (hm : ∀ E e i,(tape E e i).length≤m) :
    (edgesWork hostIndices Q w hw t eligible host tape h l).2≤
      1+l.length*(hostIndices.length*(m*(distanceBudget n+2)+5)+4) := by
  induction l with
  | nil => simp [edgesWork_nil]
  | cons e es ih =>
    have hh := hostWork_cost_le Q w hw t eligible host tape
      (edgesWork hostIndices Q w hw t eligible host tape h es).1 e (hostIndices) m
      (fun i _ _ => hm _ _ i)
    simp only [edgesWork_cons,List.length_cons]
    nlinarith

/-- The measured program has exactly the existing empirical output, together
with its explicit loop budget. Accuracy is not assumed for this equality. -/
 theorem measured_run_spec [Fintype J] (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) (J))
    (h : ℕ) (l : List (Sym2 (Fin n))) (m : ℕ)
    (hm : ∀ E e i,(tape E e i).length≤m) (hIndices : hostIndices.toFinset = (univ : Finset J)) :
    (edgesWork hostIndices Q w hw t eligible host tape h l).1=
      CorrectedVoting.edges Q (fun e => (w e:ℝ)) (t:ℝ) eligible host tape h l ∧
    (edgesWork hostIndices Q w hw t eligible host tape h l).2≤
      1+l.length*(hostIndices.length*(m*(distanceBudget n+2)+5)+4) :=
  ⟨(edgesWork_value hostIndices Q w hw t eligible host tape h l hIndices).trans
      (edges_eq Q w hw t eligible host tape h l),
    edgesWork_cost_le hostIndices Q w hw t eligible host tape h l m hm⟩

/-- The actual finite assignment tapes have exactly m entries, so their
execution budget requires no supplied accuracy or sample-length assumption. -/
 theorem assignment_run_spec [Fintype J] (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (J))
    (host : J → Finset (Sym2 (Fin n))) (m : ℕ)
    (a : CorrectedVoting.Assignment (Fin n) (J) m)
    (h : ℕ) (l : List (Sym2 (Fin n))) (hIndices : hostIndices.toFinset = (univ : Finset J)) :
    (edgesWork hostIndices Q w hw t eligible host (CorrectedVoting.assignmentTape a) h l).1=
      CorrectedVoting.edges Q (fun e => (w e:ℝ)) (t:ℝ) eligible host
        (CorrectedVoting.assignmentTape a) h l ∧
    (edgesWork hostIndices Q w hw t eligible host (CorrectedVoting.assignmentTape a) h l).2≤
      1+l.length*(hostIndices.length*(m*(distanceBudget n+2)+5)+4) := by
  apply measured_run_spec hostIndices Q w hw t eligible host (CorrectedVoting.assignmentTape a) h l m
  · intro E e i
    simp [CorrectedVoting.assignmentTape]
  · exact hIndices
end LightEFTSpanners.CorrectedExecution
