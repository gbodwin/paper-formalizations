import DirectedFlowCutGap.BinaryWeakDecomposition

/-! The successful part of the executable sampler is a normalized weak
decomposition law on cuts, with the original-weight deletion bound. -/
namespace DirectedFlowCutGap.SelectedWeakCutLaw

open scoped ENNReal
open FiniteAmplification (probability probability_eq_sum)
open BinaryWeakDecomposition RandomizedEdgeFamily RationalEdgeDecomposition

private theorem probability_some {A : Type} [Fintype A] (p : PMF (Option A)) (P : A → Prop)
    [DecidablePred P] :
    probability p (fun o => ∃ a ∈ o, P a) = ∑ a, if P a then (p (some a)).toReal else 0 := by
  classical
  rw [probability_eq_sum,Fintype.sum_option]
  have event (i : A) : (∃ a, i = a ∧ P a) ↔ P i := by
    constructor
    · rintro ⟨_,rfl,h⟩
      exact h
    · intro h
      exact ⟨_,rfl,h⟩
  simp only [Option.not_mem_none,false_and,exists_false,ite_false,zero_add,Option.mem_some_iff,event]

private theorem accepted_mass {A : Type} [Fintype A] (p : PMF (Option A)) :
    probability p (fun o => o.isSome)=(∑' a : A, p (some a)).toReal := by
  have events : (fun o : Option A => ∃ a ∈ o, True)=(fun o => (o.isSome : Prop)) := by
    funext o
    apply propext
    cases o <;> simp
  rw [← events,probability_some,tsum_fintype,ENNReal.toReal_sum (fun a _ => p.apply_ne_top (some a))]
  simp

private theorem sum_some {A : Type} [Fintype A] (p : PMF (Option A)) :
    p none+(∑' a : A, p (some a))=1 := by
  have h := p.tsum_coe
  rw [tsum_fintype,Fintype.sum_option] at h
  rw [tsum_fintype]
  exact h

theorem normalize_accepted {A : Type} [Fintype A] (p : PMF (Option A)) (nontrivial : p none<1) :
    ∃ q : PMF A, (∀ a, q a=p (some a)/(∑' b : A, p (some b))) ∧
      (∀ a ∈ q.support, some a ∈ p.support) ∧
      ∀ (P : A → Prop) [DecidablePred P],
        probability q P=probability p (fun o => ∃ a ∈ o, P a) / probability p (fun o => o.isSome) := by
  classical
  let mass := ∑' a : A, p (some a)
  have sum : p none+mass=1 := sum_some p
  have massPositive : mass≠0 := by
    intro h
    rw [h,add_zero] at sum
    exact nontrivial.ne sum
  have massFinite : mass≠∞ := by
    intro h
    rw [h,add_top] at sum
    exact ENNReal.one_ne_top sum.symm
  let q := PMF.normalize (fun a : A => p (some a)) massPositive massFinite
  refine ⟨q,fun a => ?_,fun a h => ?_,?_⟩
  · exact (PMF.normalize_apply ..).trans (div_eq_mul_inv ..).symm
  · have active : q a ≠ 0 := (PMF.mem_support_iff _ _).mp h
    apply (PMF.mem_support_iff p (some a)).mpr
    intro zero
    exact active (by simp only [q,PMF.normalize_apply,zero,zero_mul])
  · intro P inst
    rw [probability_eq_sum,probability_some,accepted_mass,div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases yes : P a
    · simp only [yes,ite_true,q,PMF.normalize_apply,ENNReal.toReal_mul,ENNReal.toReal_inv]
    · simp only [yes,ite_false,zero_mul]

theorem verified (ε : ℝ) (positive : 0<ε) :
    ∃ k M : ℕ, 0<k ∧ 0<M ∧
    ∀ (n : ℕ), 2≤n → ∀ (adj : BinaryFractionalWalkOracle.Adjacency n)
      (w : RationalEdgeThresholds.Weights n) (κ : ℕ), 0<κ →
      let D := calibratedParameters k M (κ+1) adj w
      let T := EncodedVertexAmplification.confidenceExponent n (κ+1)
      let bits := readBudgetFor D T
      let p := (EncodedSolverBits.fairTape bits).map (fun tape => ((run k M κ adj w tape).map Result.cut).join)
      ∃ law : PMF (Finset (Edge n)),
        (∀ X, law X=p (some X)/(∑' Y : Finset (Edge n), p (some Y))) ∧
        (∀ X ∈ law.support, Good adj w X) ∧
        ∀ e, probability law (fun X => e ∈ X) ≤
          8*(originalWeight adj w e:ℝ)*(8*(M:ℝ)*(n:ℝ)^ε*(originalTotal adj w:ℝ)^(1/2:ℝ)) := by
  obtain ⟨k,M,hk,hM,h⟩ := calibrated_selected ε positive
  refine ⟨k,M,hk,hM,?_⟩
  intro n hn adj w κ hκ
  dsimp only
  obtain ⟨failure,valid,marginal,_⟩ := h n hn adj w κ
  let bits := readBudgetFor (calibratedParameters k M (κ+1) adj w)
    (EncodedVertexAmplification.confidenceExponent n (κ+1))
  let p := (EncodedSolverBits.fairTape bits).map (fun tape => ((run k M κ adj w tape).map Result.cut).join)
  have pFail : p none ≤ ENNReal.ofReal ((n:ℝ)^(-(κ:ℝ))) := failure
  have bound : ((n:ℝ)^(-(κ:ℝ)))<1 := by
    have two : (2:ℝ)≤n := by exact_mod_cast hn
    have exp : (0:ℝ)<κ := by exact_mod_cast hκ
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have pNontrivial : p none<1 := pFail.trans_lt (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1) |>.mpr bound)
  obtain ⟨law,value,support,cond⟩ := normalize_accepted p pNontrivial
  refine ⟨law,value,fun X hx => valid X (support X hx),?_⟩
  intro e
  rw [cond]
  have pos : 0<probability p (fun o => o.isSome) := by
    rw [accepted_mass]
    have sum := sum_some p
    have above : (∑' a : Finset (Edge n), p (some a))≠0 := by
      intro zero
      rw [zero,add_zero] at sum
      exact pNontrivial.ne sum
    have finite : (∑' a : Finset (Edge n), p (some a))≠∞ := by
      intro top
      rw [top,add_top] at sum
      exact ENNReal.one_ne_top sum.symm
    exact ENNReal.toReal_pos above finite
  exact (div_le_iff₀ pos).mpr (marginal e)

end DirectedFlowCutGap.SelectedWeakCutLaw
