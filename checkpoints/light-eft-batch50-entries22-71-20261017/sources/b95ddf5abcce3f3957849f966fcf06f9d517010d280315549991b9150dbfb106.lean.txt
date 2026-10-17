import LightSpanners.BucketPadding
import LightSpanners.BucketUniqueness

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- All chords in a monotone walk lie above the lower endpoint of the first
nonempty bucket, and its first chord lies in that same bucket. -/
theorem BucketMonotoneWalk.first_bucket {u v : V} {eps : ℝ} {k J : ℕ} {p : G.Walk u v}
    (hp : C.BucketMonotoneWalk eps k true J p) {e : Sym2 V} {es : List (Sym2 V)}
    (he : C.chordEdges p=e::es) :
    ∃ j<J, (2:ℝ)^j≤w e ∧ w e<2^(j+1) ∧ ∀ f∈C.chordEdges p, (2:ℝ)^j≤w f := by
  induction hp generalizing e es with
  | nil u => simp at he
  | @snoc J u v z p q hp hq ih =>
    have hw := hq.choose_spec.1.2.1
    rw [C.chordEdges_append] at he
    cases ha : C.chordEdges p with
    | nil =>
      have hb : C.chordEdges q=e::es := by simpa [ha] using he
      have hwe := hw e (by simp [hb])
      refine ⟨J,by omega,hwe.1,hwe.2,?_⟩
      intro f hf
      rw [C.chordEdges_append,ha,List.nil_append] at hf
      exact (hw f hf).1
    | cons e' es' =>
      have hee : e'=e := by simpa [ha] using (congrArg List.head? he)
      subst e'
      obtain ⟨j,hj,hje,hje',hmin⟩ := ih ha
      refine ⟨j,by omega,hje,hje',?_⟩
      intro f hf
      rw [C.chordEdges_append,List.mem_append] at hf
      rcases hf with hf | hf
      · exact hmin f hf
      · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : j≤J)).trans (hw f hf).1

/-- Padding all nonempty blocks by the same number of forward/backward
steps produces a safe walk with consistently shifted endpoints. Empty blocks
remain actual empty walks, without creating an immediate turnaround. -/
theorem BucketMonotoneWalk.pad_above {u v : V} {eps : ℝ} {k J j t : ℕ} {p : G.Walk u v}
    (hp : C.BucketMonotoneWalk eps k true J p) (heps : 0≤eps)
    (hmin : ∀ e∈C.chordEdges p, (2:ℝ)^j≤w e) (ht : (t:ℝ)≤eps*k*2^j/2) :
    ∃ q : G.Walk ((C.successor.symm : V → V)^[t] u) ((C.successor.symm : V → V)^[t] v),
      C.BucketMonotoneWalk eps k false J q ∧ C.chordEdges q=C.chordEdges p := by
  induction hp with
  | nil u => exact ⟨.nil,.nil _,rfl⟩
  | @snoc J u v z p q hp hq ih =>
    have hpmin : ∀ e∈C.chordEdges p, (2:ℝ)^j≤w e := by
      intro e he
      apply hmin e
      rw [C.chordEdges_append]
      exact List.mem_append_left _ he
    obtain ⟨p',hp',hpword⟩ := ih hpmin
    have hblock : ∃ q' : G.Walk ((C.successor.symm : V → V)^[t] v)
        ((C.successor.symm : V → V)^[t] z),
        C.BucketSafe eps k J q' ∧ C.chordEdges q'=C.chordEdges q := by
      by_cases hzero : C.chordEdges q=[]
      · have hn := (hq.safe C).nil_of_no_chords C hzero
        cases hn
        exact ⟨.nil,C.bucketSafe_nil eps heps k J _,rfl⟩
      · obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ hzero
        have hemin : (2:ℝ)^j≤w e := by
          apply hmin e
          rw [C.chordEdges_append]
          exact List.mem_append_right _ he
        have hemax := (hq.choose_spec.1.2.1 e he).2
        have hj : j≤J := by
          by_contra hn
          have hpow : (2:ℝ)^(J+1)≤2^j := pow_le_pow_right₀ (by norm_num) (by omega)
          linarith
        have ht' : (t:ℝ)≤eps*k*2^J/2 := by
          have hpow : (2:ℝ)^j≤2^J := pow_le_pow_right₀ (by norm_num) hj
          have hm := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤eps*k)
          linarith
        exact hq.pad_safe C hzero ht'
    obtain ⟨q',hq',hqword⟩ := hblock
    refine ⟨p'.append q',.snoc hp' hq',?_⟩
    rw [C.chordEdges_append,C.chordEdges_append,hpword,hqword]

end LightSpanners.UnitSpanningCycle
