import LightEFTSpanners.CorrectedLowCompetitionFallback
import LightEFTSpanners.CorrectedLowCompetitionParameters
import LightEFTSpanners.CorrectedLowCompetitionCycle

/-! Literal finite-order lower bounds below competition 2f. The cycle family
handles large orders; the proved unit-ratio input handles the remaining orders.
All constants are uniform in n, f, stretch, k, and epsilon. -/
namespace LightEFTSpanners.CorrectedLowCompetition
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

theorem corrected_low_competition_real_every_order {n f q : ℕ} {t : ℝ}
    (hn : 2≤n) (hf : 1≤f) (hq : q≤2*f-1) (ht : 1≤t) :
    ∃ G : SimpleGraph (Fin n), ∃ W : Sym2 (Fin n) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin n), IsEFTSpanner G H W t f →
        ∀Q : SimpleGraph (Fin n), IsMinimumFTPreserver G Q W q →
          (n:ℝ)/(32*(f:ℝ)^2*t)≤competitiveLightness H Q W) := by
  by_cases hlarge : (2*⌈t⌉₊+1)*(f+1)≤n
  · have hquot := large_cycle_quotient ht hlarge
    let m := n/(f+1)-3
    have hm3 : m+3=n/(f+1) := by dsimp [m]; omega
    have hvc : Fintype.card (ParallelSubdivision.Vertex (I:=Fin f) (cycleGraph (m+3)))=
        n/(f+1)*(f+1) := by
      rw [ParallelSubdivision.cycle_vertex_card_at,hm3]
      ring
    have hcard : Fintype.card (ParallelSubdivision.Vertex (I:=Fin f) (cycleGraph (m+3)))≤n := by
      rw [hvc]
      exact Nat.div_mul_le_self n (f+1)
    have hhalf : n≤2*Fintype.card (ParallelSubdivision.Vertex (I:=Fin f) (cycleGraph (m+3))) := by
      rw [hvc]
      exact quotient_order_half (by omega) (by omega)
    exact exists_cycle_padding_lower m f q n (by omega) hq t ht hquot.2 hcard hhalf
  · obtain ⟨G,W,hpos,hbound⟩ := exists_unit_ratio (n:=n) (f:=f) (q:=q) (t:=t) hn
    refine ⟨G,W,hpos,?_⟩
    intro H hsp Q hQ
    rw [hbound H hsp Q hQ]
    exact small_order_ratio_le_one hf ht hlarge

/-- Uniform in epsilon on precisely the corrected hypothesis 0<eps≤1/k. -/
theorem corrected_low_competition_intro_every_order {n f k q : ℕ} {eps : ℝ}
    (hn : 2≤n) (hf : 1≤f) (hk : 1≤k) (hq : q≤2*f-1)
    (heps : 0<eps) (hsmall : eps≤1/(k:ℝ)) :
    ∃ G : SimpleGraph (Fin n), ∃ W : Sym2 (Fin n) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin n),
        IsEFTSpanner G H W ((1+eps)*(2*(k:ℝ)-1)) f →
        ∀Q : SimpleGraph (Fin n), IsMinimumFTPreserver G Q W q →
          (n:ℝ)/(96*(f:ℝ)^2*(k:ℝ))≤competitiveLightness H Q W) := by
  have hstretch := introStretch_bounds hk heps hsmall
  obtain ⟨G,W,hpos,hbound⟩ := corrected_low_competition_real_every_order hn hf hq hstretch.1
  refine ⟨G,W,hpos,?_⟩
  intro H hsp Q hQ
  apply le_trans ?_ (hbound H hsp Q hQ)
  have hfR : (0:ℝ)<f := by exact_mod_cast (show 0<f by omega)
  have htpos : 0 < introStretch k eps := by linarith [hstretch.1]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg n)
    (by positivity : (0:ℝ)<32*(f:ℝ)^2*introStretch k eps)
  nlinarith [mul_le_mul_of_nonneg_left hstretch.2 (by positivity : (0:ℝ)≤32*(f:ℝ)^2)]

/-- Theorem 9 with its displayed integer stretch and competition f, for every
nontrivial prescribed order and a uniform explicit lower-bound constant. -/
theorem corrected_theorem9_every_order {n f k : ℕ}
    (hn : 2≤n) (hf : 1≤f) (hk : 1≤k) :
    ∃ G : SimpleGraph (Fin n), ∃ W : Sym2 (Fin n) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin n), IsEFTSpanner G H W (k:ℝ) f →
        ∀Q : SimpleGraph (Fin n), IsMinimumFTPreserver G Q W f →
          (n:ℝ)/(32*(f:ℝ)^2*(k:ℝ))≤competitiveLightness H Q W) :=
  corrected_low_competition_real_every_order hn hf (by omega) (by exact_mod_cast hk)

/-- Theorem 10's lower branch, with competition 2f-1 and the accepted epsilon
hypothesis, now at every n≥2 with a constant independent of epsilon and f,k. -/
theorem corrected_theorem10_lower_every_order {n f k : ℕ} {eps : ℝ}
    (hn : 2≤n) (hf : 1≤f) (hk : 1≤k)
    (heps : 0<eps) (hsmall : eps≤1/(k:ℝ)) :
    ∃ G : SimpleGraph (Fin n), ∃ W : Sym2 (Fin n) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin n),
        IsEFTSpanner G H W ((1+eps)*(2*(k:ℝ)-1)) f →
        ∀Q : SimpleGraph (Fin n), IsMinimumFTPreserver G Q W (2*f-1) →
          (n:ℝ)/(96*(f:ℝ)^2*(k:ℝ))≤competitiveLightness H Q W) :=
  corrected_low_competition_intro_every_order hn hf hk le_rfl heps hsmall

end LightEFTSpanners.CorrectedLowCompetition
