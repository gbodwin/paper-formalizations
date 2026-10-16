import LightEFTSpanners.ExecutableVotingWork
namespace LightEFTSpanners.ExecutableVoting.WorkPilotComparison
open SimpleGraph LightSpanners RationalDistance Finset
variable {n j : ℕ}
def sampleWork (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) :
    List (Finset (Sym2 (Fin n))) → ℕ × ℕ :=
  List.rec (0,1) (fun S _ r =>
    let z := coveredWork (sampled Q E T S) w hw t e
    (r.1+(if z.1 then 0 else 1),r.2+z.2+2))

 theorem sampleWork_eq_prior (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) (l : List (Finset (Sym2 (Fin n)))) :
    sampleWork Q E T w hw t e l = LightEFTSpanners.ExecutableVoting.sampleWork Q E T w hw t e l := by
  induction l with
  | nil => rfl
  | cons S ss ih =>
    simp only [sampleWork] at ih ⊢
    simp only [LightEFTSpanners.ExecutableVoting.sampleWork]
    rw [ih]
#print axioms sampleWork_eq_prior

def hostWork (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : List (Fin j) → Finset (Fin j) × ℕ :=
  List.rec (∅,1) (fun i _ r =>
    if i∈eligible e then
      let z := sampleWork Q E (host i) w hw t e (tape E e i)
      (if (3:ℚ)/8≤(z.1:ℚ)/(tape E e i).length then insert i r.1 else r.1,r.2+z.2+4)
    else (r.1,r.2+1))

 theorem hostWork_eq_prior (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (l : List (Fin j)) :
    hostWork Q w hw t eligible host tape E e l = LightEFTSpanners.ExecutableVoting.hostWork Q w hw t eligible host tape E e l := by
  induction l with
  | nil => rfl
  | cons i is ih =>
    simp only [hostWork] at ih ⊢
    simp only [LightEFTSpanners.ExecutableVoting.hostWork]
    rw [ih]
    simp only [sampleWork_eq_prior]
#print axioms hostWork_eq_prior

def edgesWork (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (h : ℕ) : List (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) × ℕ :=
  List.rec (Q,1) (fun e _ r =>
    let z := hostWork Q w hw t eligible host tape r.1 e (List.finRange j)
    (if h≤z.1.card then insert e r.1 else r.1,r.2+z.2+3))

 theorem edgesWork_eq_prior (Q : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) (Fin j))
    (h : ℕ) (l : List (Sym2 (Fin n))) :
    edgesWork Q w hw t eligible host tape h l = LightEFTSpanners.ExecutableVoting.edgesWork Q w hw t eligible host tape h l := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    simp only [edgesWork] at ih ⊢
    simp only [LightEFTSpanners.ExecutableVoting.edgesWork]
    rw [ih]
    simp only [hostWork_eq_prior]
#print axioms edgesWork_eq_prior

end LightEFTSpanners.ExecutableVoting.WorkPilotComparison
