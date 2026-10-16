import LightEFTSpanners.SampleVoteTrace

/-! Fixed-fuel execution and its exact empirical-vote contract. The sample
count header and per-cell input records are represented input data. -/
namespace LightEFTSpanners.SampleVote
open Controller SampleRecords
 def bound (n sampleCount : ℕ) : ℕ := sampleCount*perSample n+1
 def execute (n sampleCount u v : ℕ) (budget : ℚ) (records : List Records) : Bool :=
  match Controller.run (transition n u v budget) (bound n sampleCount) (.samples records 0 0) with
  | .halt b => b
  | _ => false
 theorem run_encoded {n : ℕ} (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (budget : ℚ) (draws : List (Finset (Sym2 (Fin n)))) :
    Controller.run (transition n u.val v.val budget) (bound n draws.length)
      (.samples (encoded Q E T w draws) 0 0)=
      .halt (finish (failures Q E T w u v budget draws) draws.length) := by
  obtain ⟨k,hk,ht⟩ := samples_trace Q E T w u v budget draws 0 0
  simp only [zero_add] at ht
  have he : bound n draws.length=k+(bound n draws.length-k) := by unfold bound;omega
  rw [he,Controller.run_add,ht.run_eq]
  exact Controller.run_terminal (transition n u.val v.val budget)
    (.halt (finish (failures Q E T w u v budget draws) draws.length)) rfl _
 theorem execute_encoded {n : ℕ} (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (budget : ℚ) (draws : List (Finset (Sym2 (Fin n)))) :
    execute n draws.length u.val v.val budget (encoded Q E T w draws)=
      finish (failures Q E T w u v budget draws) draws.length := by
  simp only [execute,run_encoded]
 theorem finish_iff_ratio (f c : ℕ) : finish f c=true ↔ (3:ℚ)/8≤(f:ℚ)/c := by
  by_cases hc : c=0
  · subst c;simp [finish]
  have hcp : 0<c := Nat.pos_of_ne_zero hc
  have hq : (0:ℚ)<c := by exact_mod_cast hcp
  have he : ((3:ℚ)/8≤(f:ℚ)/c) ↔ (3:ℚ)*c≤8*f := by
    rw [le_div_iff₀ hq]
    constructor <;> intro h <;> linarith
  rw [he]
  simp only [finish,decide_eq_true_eq,hcp,true_and]
  exact_mod_cast (Iff.rfl : 3*c≤8*f ↔ 3*c≤8*f)
 theorem execute_iff_estimate {n : ℕ} (Q E T : Finset (Sym2 (Fin n)))
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) (u v : Fin n)
    (draws : List (Finset (Sym2 (Fin n)))) :
    execute n draws.length u.val v.val (t*w s(u,v)) (encoded Q E T w draws)=true ↔
      (3:ℚ)/8≤ExecutableVoting.estimate Q E T w hw t s(u,v) draws := by
  rw [execute_encoded,finish_iff_ratio]
  rfl
 theorem represented_vote_correct {n : ℕ} (Q E T : Finset (Sym2 (Fin n)))
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) (u v : Fin n)
    (draws : List (Finset (Sym2 (Fin n)))) (records : List Records) (sampleCount : ℕ)
    (hrecords : records=encoded Q E T w draws) (hcount : sampleCount=draws.length) :
    (execute n sampleCount u.val v.val (t*w s(u,v)) records=true ↔
      (3:ℚ)/8≤ExecutableVoting.estimate Q E T w hw t s(u,v) draws) ∧
    ∃ k,k≤bound n sampleCount ∧ Trace (transition n u.val v.val (t*w s(u,v))) k
      (.samples records 0 0) (.halt (execute n sampleCount u.val v.val (t*w s(u,v)) records)) := by
  subst records;subst sampleCount
  refine ⟨execute_iff_estimate Q E T w hw t u v draws,?_⟩
  rw [execute_encoded]
  simpa only [zero_add,bound] using samples_trace Q E T w u v (t*w s(u,v)) draws 0 0
/-- The exact represented caller vote is the corresponding vote in the
already proved real-weight empirical recursion. Eligibility remains a supplied
host-list contract; no cost for that outer loop is asserted here. -/
 theorem mem_real_votes_iff {n : ℕ} {J : Type*} [DecidableEq J]
    (Q E : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e)
    (t : ℚ) (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (tape : SampledGreedy.Tape (Fin n) J) (u v : Fin n) (j : J) :
    j∈SampledGreedy.votes Q (fun d => (w d:ℝ)) (t:ℝ) eligible host tape E s(u,v) ↔
      j∈eligible s(u,v) ∧ execute n (tape E s(u,v) j).length u.val v.val (t*w s(u,v))
        (encoded Q E (host j) w (tape E s(u,v) j))=true := by
  rw [←ExecutableVoting.votes_eq Q w hw t eligible host tape E s(u,v)]
  simp only [ExecutableVoting.votes,Finset.mem_filter]
  rw [execute_iff_estimate Q E (host j) w hw t u v (tape E s(u,v) j)]
end LightEFTSpanners.SampleVote
