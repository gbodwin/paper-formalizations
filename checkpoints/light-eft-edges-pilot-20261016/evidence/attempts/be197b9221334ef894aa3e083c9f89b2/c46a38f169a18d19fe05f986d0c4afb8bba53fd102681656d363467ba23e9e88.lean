import LightEFTSpanners.LogarithmicVotingSamples

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset FiniteProbability
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A computable polynomial oversampling count, avoiding exact real logarithm evaluation. -/
def polynomialRepetitions (n s : ℕ) : ℕ := 32*(s+5)*n+1

theorem polynomialRepetitions_pos (n s : ℕ) : 0<polynomialRepetitions n s := Nat.succ_pos _

theorem polynomialRepetitions_bound (n s : ℕ) :
    32*((s+5:ℕ):ℝ)*Real.log n≤(polynomialRepetitions n s:ℝ) := by
  have h := Real.log_le_self (show (0:ℝ)≤n by positivity)
  have hm := mul_le_mul_of_nonneg_left h (show (0:ℝ)≤32*((s+5:ℕ):ℝ) by positivity)
  unfold polynomialRepetitions
  push_cast at hm ⊢
  linarith
 theorem polynomial_inaccurate_probability (G Q : SimpleGraph V) (w : Sym2 V → ℝ)
    (t : ℝ) (q f h s : ℕ) (hf : 0<f) (hQ : IsFTConnectivityPreserver G Q q)
    (F : Fin (q+1) → SimpleGraph V) :
    (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
      (polynomialRepetitions (Fintype.card V) s) (input G Q w)).prob (fun a =>
        ¬AccurateTrace Q.edgeFinset w t f (componentEligible univ F) (componentHost F)
          (assignmentTape a) h (input G Q w)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  classical
  by_cases hn : 2≤Fintype.card V
  · have hh := execution_inaccurate_probability Q.edgeFinset w t f hf
      (polynomialRepetitions (Fintype.card V) s) (polynomialRepetitions_pos _ _)
      (componentEligible univ F) (componentHost F) h (input G Q w) (input_nodup G Q w)
    have hcount : (((input G Q w).map (fun e => (componentEligible univ F e).card)).sum:ℝ)≤
        (Fintype.card V:ℝ)^4 := by exact_mod_cast constructed_query_count_le G Q w q hQ F
    exact hh.trans ((mul_le_mul_of_nonneg_right hcount (by positivity)).trans
      (exponential_union_bound _ s _ hn (polynomialRepetitions_bound _ _)))
  · have hsat : Fintype.card V≤q+2 := by omega
    have he := preserver_eq_at_large_budget hQ hsat
    have hi : input G Q w=[] := by
      rw [he]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      have hh := (mem_input G G w e).mp he
      exact hh.2 hh.1
    rw [hi]
    simp only [executionLaw,Law.prob_pure,AccurateTrace,not_true_eq_false,ite_false]
    positivity

end LightEFTSpanners.SampledGreedy
