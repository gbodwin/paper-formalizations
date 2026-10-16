import LightEFTSpanners.SampleVoteMachine

/-! A counted successful trace for the complete per-host sample vote. The
input record list is consumed in order; every submachine step is included. -/
namespace LightEFTSpanners.SampleVote
open Controller SampleRecords
 theorem one_sample_trace {n : ℕ} (Q E T S : Finset (Sym2 (Fin n)))
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) (rs : List Records) (f c : ℕ) :
    ∃ k,k≤perSample n ∧ Trace (transition n u.val v.val budget) k
      (.samples (SampleRecords.encode Q E T S w::rs) f c)
      (.samples rs (f+(if RationalDistance.shortTest (ExecutableVoting.sampled Q E T S) w u v budget then 0 else 1)) (c+1)) := by
  let R := SampleRecords.encode Q E T S w
  have hmat := materialize_trace R
  have hR : R.length=n := by simp [R,SampleRecords.encode]
  have hC : cellCount R=n*n := encode_cellCount Q E T S w
  have hV := encode_values Q E T S w
  change values 0 R=_ at hV
  obtain ⟨k,hk,htrace⟩ := LinkedDistance.machine_shortTest (ExecutableVoting.sampled Q E T S) w u v budget
  have h₀ := Trace.one (show transition n u.val v.val budget (.samples (R::rs) f c)=
    some (.materialize rs f c (.row 0 R [])) from rfl)
  have h₁ := materialize_lift n u.val v.val budget rs f c hmat
  have h₂ := Trace.one (show transition n u.val v.val budget (.materialize rs f c (.halt (values 0 R)))=
    some (.distance rs f c (values 0 R) (.init n 0 [])) from rfl)
  have h₃ := distance_lift n u.val v.val budget rs f c _ htrace
  rw [←hV] at h₃
  have h₄ := Trace.one (show transition n u.val v.val budget
      (.distance rs f c (values 0 R) (.halt (RationalDistance.shortTest (ExecutableVoting.sampled Q E T S) w u v budget)))=
      some (.samples rs (f+(if RationalDistance.shortTest (ExecutableVoting.sampled Q E T S) w u v budget then 0 else 1)) (c+1)) from rfl)
  refine ⟨1+(2*cellCount R+4*R.length+2)+(1+k+1),?_,?_⟩
  · unfold perSample LinkedDistance.bound at *
    rw [hC,hR]
    simp only [Nat.mul_assoc]
    omega
  · simpa only [Nat.add_assoc] using h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))
 def failures {n : ℕ} (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (budget : ℚ) (draws : List (Finset (Sym2 (Fin n)))) : ℕ :=
  (draws.filter fun S => !(RationalDistance.shortTest (ExecutableVoting.sampled Q E T S) w u v budget)).length
 theorem samples_trace {n : ℕ} (Q E T : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (budget : ℚ) (draws : List (Finset (Sym2 (Fin n)))) (f c : ℕ) :
    ∃ k,k≤draws.length*perSample n+1 ∧ Trace (transition n u.val v.val budget) k
      (.samples (encoded Q E T w draws) f c)
      (.halt (finish (f+failures Q E T w u v budget draws) (c+draws.length))) := by
  induction draws generalizing f c with
  | nil => exact ⟨1,by simp,Trace.one (by simp [transition,encoded,failures])⟩
  | cons S ss ih =>
    obtain ⟨k,hk,ht⟩ := one_sample_trace Q E T S w u v budget (encoded Q E T w ss) f c
    obtain ⟨l,hl,hs⟩ := ih (f+(if RationalDistance.shortTest (ExecutableVoting.sampled Q E T S) w u v budget then 0 else 1)) (c+1)
    refine ⟨k+l,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul];omega
    · have h := ht.trans hs
      cases hb : RationalDistance.shortTest (ExecutableVoting.sampled Q E T S) w u v budget <;>
        simpa [encoded,failures,hb,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
end LightEFTSpanners.SampleVote
