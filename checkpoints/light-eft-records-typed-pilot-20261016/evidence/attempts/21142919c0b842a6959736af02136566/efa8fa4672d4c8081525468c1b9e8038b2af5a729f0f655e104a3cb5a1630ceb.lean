import LightEFTSpanners.SampledHistoryWeight
import Mathlib.Data.Finset.Max

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners LightSpanners.FiniteSampling
variable {V J : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

noncomputable def assignedWeight (w : Sym2 V → ℝ) (j : J) :
    List (Sym2 V × Finset J) → ℝ
  | [] => 0
  | (e,A)::rs => (if j∈A then w e else 0)+assignedWeight w j rs

/-- The literal accepted-host history and exact finite sampling law yield
expected retained non-seed weight at least its assigned weight divided by8f. -/
theorem expected_retained_host_weight (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f h : ℕ) (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (rs : List (Sym2 V × Finset J)) (j : J) (hf : 0<f) (hTQ : host j⊆Q)
    (hn : (rs.map Prod.fst).Nodup) (hdis : ∀ e∈rs.map Prod.fst,e∉Q)
    (hw : ∀ e∈rs.map Prod.fst,0≤w e)
    (hgood : ApprovedHistory Q w t f h eligible host rs) :
    assignedWeight w j rs/(8*(f:ℝ))≤
      expectedRetainedWeight (host j) w t (1/(2*(f:ℝ))) j rs := by
  induction rs with
  | nil => simp [assignedWeight,expectedRetainedWeight,retainedWeight,selectedList,greedyEdges]
  | cons r rs ih =>
    obtain ⟨e,A⟩ := r
    obtain ⟨heR,hn⟩ := List.nodup_cons.mp hn
    obtain ⟨hprev,_,_,hprob⟩ := hgood
    have hin (d) (hd : d∈rs.map Prod.fst) : d∈((e,A)::rs).map Prod.fst :=
      List.mem_cons_of_mem e hd
    have hdis' := fun d hd => hdis d (hin d hd)
    have hwe : 0≤w e := hw e (by simp)
    have hi := ih hn hdis' (fun d hd => hw d (hin d hd)) hprev
    have heT : e∉host j := fun he => hdis e (by simp) (hTQ he)
    rw [expectedRetainedWeight_cons _ _ _ _ _ _ _ _ heT heR]
    by_cases hj : j∈A
    · have hp := (hprob j hj).trans
        (sampled_prefix_rejection_probability Q (host j) w t f j rs e hf hdis')
      have heq : (∑ S∈(rs.map Prod.fst).toFinset.powerset,
          mass (rs.map Prod.fst).toFinset (1/(2*(f:ℝ))) S*
            (if j∈A ∧ ¬FTCovered (edgeGraph (greedyEdges (host j) w t 0 (selectedList j S rs))) w t 0 e
              then w e else 0))=
          (∑ S∈(rs.map Prod.fst).toFinset.powerset,
            mass (rs.map Prod.fst).toFinset (1/(2*(f:ℝ))) S*
              (if ¬FTCovered (edgeGraph (greedyEdges (host j) w t 0 (selectedList j S rs))) w t 0 e
                then 1 else 0))*w e := by
        rw [sum_mul]
        apply sum_congr rfl
        intro S _
        simp only [hj,true_and]
        split_ifs <;> ring
      rw [heq]
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hwe)
        (show (0:ℝ)≤1/(2*(f:ℝ)) by positivity)
      have heq' : (1/(2*(f:ℝ)))*((1/4)*w e)=w e/(8*(f:ℝ)) := by ring
      rw [heq'] at hh
      simp only [assignedWeight,hj,ite_true,add_div]
      linarith
    · simpa only [assignedWeight,hj,ite_false,zero_add,false_and,mul_zero,sum_const_zero,
        add_zero] using hi

/-- The finite maximum sample attains the proved expected retained weight.
The returned sample and retained graph use actual edge identities. -/
theorem exists_heavy_retained_host_sample (Q : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f h : ℕ) (eligible : Sym2 V → Finset J) (host : J → Finset (Sym2 V))
    (rs : List (Sym2 V × Finset J)) (j : J) (hf : 0<f) (hTQ : host j⊆Q)
    (hn : (rs.map Prod.fst).Nodup) (hdis : ∀ e∈rs.map Prod.fst,e∉Q)
    (hw : ∀ e∈rs.map Prod.fst,0≤w e)
    (hgood : ApprovedHistory Q w t f h eligible host rs) :
    ∃ S⊆(rs.map Prod.fst).toFinset,assignedWeight w j rs/(8*(f:ℝ))≤
      retainedWeight (host j) w t j S rs := by
  classical
  obtain ⟨S,hS,hmax⟩ := exists_max_image (rs.map Prod.fst).toFinset.powerset
    (fun S => retainedWeight (host j) w t j S rs) ⟨∅,mem_powerset.mpr (empty_subset _)⟩
  refine ⟨S,mem_powerset.mp hS,?_⟩
  have hf1 : (1:ℝ)≤f := by exact_mod_cast hf
  have hp1 : 1/(2*(f:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
  apply (expected_retained_host_weight Q w t f h eligible host rs j hf hTQ hn hdis hw hgood).trans
  unfold expectedRetainedWeight
  calc
    _ ≤ ∑ A∈(rs.map Prod.fst).toFinset.powerset,
        mass (rs.map Prod.fst).toFinset (1/(2*(f:ℝ))) A*retainedWeight (host j) w t j S rs := by
      apply sum_le_sum
      intro A hA
      exact mul_le_mul_of_nonneg_left (hmax A hA) (mass_nonneg _ _ (by positivity) hp1)
    _ = _ := by rw [←sum_mul,sum_mass,one_mul]
end LightEFTSpanners.SampledGreedy
