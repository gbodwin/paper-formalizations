import LinearDistancePreservers.UnweightedClique
import LinearDistancePreservers.TheoremFourRateAudit
import Mathlib.Data.Nat.Choose.Cast

/-! An actual graph lower bound for the small-deficit range of the
displayed expression in Theorem 4. The rate audit bounds that expression
by T²/4 under an explicit size condition, and a padded clique supplies
the witness. This does not prove the remaining range or the printed
superquadratic corollary. -/
namespace LinearDistancePreservers.TheoremFourDense
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

noncomputable def displayedBound (N T : ℕ) (d c : ℝ) : ℝ :=
  (N : ℝ)^(2/(d+1)) * (T : ℝ)^((2*d+1)*(d-1)/(d*(d+1))) *
    Real.exp (-c*Real.sqrt (Real.log (N : ℝ)))

theorem quarter_square_le_choose {T : ℕ} (hT : 2 ≤ T) :
    (T : ℝ)^2/4 ≤ (T.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  have h : (2 : ℝ) ≤ T := by exact_mod_cast hT
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ T) (sub_nonneg.mpr h)]

/-- The literal displayed rate is attained by an unweighted graph with
exactly N vertices and T terminals in this explicit small-deficit range.
The dimension may be any real d≥1, hence includes the paper's dimensions. -/
theorem displayed_bound_of_small_deficit {N T : ℕ} {d K c : ℝ}
    (hT : 2 ≤ T) (hTN : T ≤ N) (hd : 1 ≤ d) (hK : 0 ≤ K)
    (ht : 0 ≤ (2/3)*Real.log (N : ℝ)-Real.log (T : ℝ))
    (hdeficit : (2/3)*Real.log (N : ℝ)-Real.log (T : ℝ) ≤
      K*Real.sqrt (Real.log (N : ℝ)))
    (hlarge : 27*K^2/8+Real.log 4 ≤ c*Real.sqrt (Real.log (N : ℝ))) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        displayedBound N T d c ≤ (H.edgeFinset.card : ℝ) := by
  classical
  have hTnat : 0 < T := by omega
  have hNnat : 1 < N := by omega
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hTnat
  have hNpos : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hratio := TheoremFourRateAudit.suppressed_expression_le
    (N := (N : ℝ)) (sigma := (T : ℝ)) (d := d)
    (t := (2/3)*Real.log (N : ℝ)-Real.log (T : ℝ))
    (K := K) (c := c) hNpos hTpos hd ht hK (by ring) hdeficit
  have hexp : Real.exp (27*K^2/8-c*Real.sqrt (Real.log (N : ℝ))) ≤
      (1/4 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by linarith)
      _ = 1/4 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; norm_num
  have hdiv : displayedBound N T d c / (T : ℝ)^2 ≤ (1/4 : ℝ) := by
    simpa only [displayedBound, div_mul_eq_mul_div] using hratio.trans hexp
  have hsmall : displayedBound N T d c ≤ (T : ℝ)^2/4 := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < (T : ℝ)^2)).mp hdiv
    nlinarith
  obtain ⟨G,S,hS,hE⟩ := UnweightedClique.clique_lower_bound hTnat hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  rw [hE H hH hp]
  exact hsmall.trans (quarter_square_le_choose hT)

end LinearDistancePreservers.TheoremFourDense
