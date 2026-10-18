import LightEFTSpanners.AdaptiveVotingConcentration
import LightEFTSpanners.VotingQueryCount

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset FiniteProbability
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Explicit logarithmic repetition count, including the final integer round. -/
noncomputable def repetitionCount (n s : ℕ) : ℕ := ⌈32*((s+5:ℕ):ℝ)*Real.log n⌉₊+1

 theorem repetitionCount_pos (n s : ℕ) : 0<repetitionCount n s := Nat.succ_pos _

 theorem repetitionCount_bound (n s : ℕ) :
    32*((s+5:ℕ):ℝ)*Real.log n ≤ (repetitionCount n s:ℝ) := by
  have h := Nat.le_ceil (32*((s+5:ℕ):ℝ)*Real.log n)
  unfold repetitionCount
  push_cast at h ⊢
  linarith

 theorem exponential_union_bound (n s m : ℕ) (hn : 2≤n)
    (hm : 32*((s+5:ℕ):ℝ)*Real.log n≤m) :
    (n:ℝ)^4*(2*Real.exp (-(m:ℝ)/32)) ≤ ((n:ℝ)^s)⁻¹ := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) hn)
  have hn2 : (2:ℝ)≤n := by exact_mod_cast hn
  have he : Real.exp (-(m:ℝ)/32) ≤ ((n:ℝ)^(s+5))⁻¹ := by
    calc
      _ ≤ Real.exp (-((s+5:ℕ):ℝ)*Real.log n) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hnR]
  calc
    _ ≤ (n:ℝ)^4*(2*((n:ℝ)^(s+5))⁻¹) := by gcongr
    _ = (2/(n:ℝ))*((n:ℝ)^s)⁻¹ := by
      rw [pow_add]
      field_simp
    _ ≤ 1*((n:ℝ)^s)⁻¹ := mul_le_mul_of_nonneg_right
      ((div_le_one hnR).mpr hn2) (by positivity)
    _ = _ := one_mul _

 theorem constructed_inaccurate_probability (G Q : SimpleGraph V) (w : Sym2 V → ℝ)
    (t : ℝ) (q f h s : ℕ) (hf : 0<f) (hQ : IsFTConnectivityPreserver G Q q)
    (F : Fin (q+1) → SimpleGraph V) :
    (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
      (repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a =>
        ¬AccurateTrace Q.edgeFinset w t f (componentEligible univ F) (componentHost F)
          (assignmentTape a) h (input G Q w)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  classical
  by_cases hn : 2≤Fintype.card V
  · have hh := execution_inaccurate_probability Q.edgeFinset w t f hf
      (repetitionCount (Fintype.card V) s) (repetitionCount_pos _ _)
      (componentEligible univ F) (componentHost F) h (input G Q w) (input_nodup G Q w)
    have hcount : (((input G Q w).map (fun e => (componentEligible univ F e).card)).sum:ℝ)≤
        (Fintype.card V:ℝ)^4 := by exact_mod_cast constructed_query_count_le G Q w q hQ F
    exact hh.trans ((mul_le_mul_of_nonneg_right hcount (by positivity)).trans
      (exponential_union_bound _ s _ hn (repetitionCount_bound _ _)))
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
