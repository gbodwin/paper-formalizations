import LightEFTSpanners.SamplingFaultAvoidance
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace LightSpanners.FiniteSampling
open Finset
variable {α : Type*} [DecidableEq α]

/-- Adding an unselected independent coordinate multiplies mass by 1-p. -/
theorem mass_insert_absent (U S : Finset α) (p : ℝ) {a : α}
    (ha : a∉U) (hS : S⊆U) : mass (insert a U) p S=(1-p)*mass U p S := by
  have haS : a∉S := fun h => ha (hS h)
  have hd : insert a U\S=insert a (U\S) := by ext x;by_cases hx : x=a <;> simp [hx,haS]
  have haD : a∉U\S := fun h => ha (mem_sdiff.mp h).1
  simp only [mass,hd,card_insert_of_notMem haD,pow_succ]
  ring

/-- Adding a selected independent coordinate multiplies mass by p. -/
theorem mass_insert_present (U S : Finset α) (p : ℝ) {a : α}
    (ha : a∉U) (hS : S⊆U) : mass (insert a U) p (insert a S)=p*mass U p S := by
  have haS : a∉S := fun h => ha (hS h)
  have hd : insert a U\insert a S=U\S := by
    ext x;by_cases hx : x=a <;> simp [hx,ha]
  simp only [mass,hd,card_insert_of_notMem haS,pow_succ]
  ring

/-- Exact marginal law when unused coordinates are integrated out. -/
theorem sum_mass_restrict_union (R D : Finset α) (p : ℝ)
    (g : Finset α → ℝ) (hdis : Disjoint R D) :
    (∑ S∈(R∪D).powerset,mass (R∪D) p S*g (S∩R))=
      ∑ A∈R.powerset,mass R p A*g A := by
  induction D using Finset.induction_on with
  | empty =>
    simp only [union_empty]
    apply sum_congr rfl
    intro S hS
    rw [inter_eq_left.mpr (mem_powerset.mp hS)]
  | @insert a D ha ih =>
    have haR : a∉R := fun h => disjoint_left.mp hdis h (mem_insert_self _ _)
    have hdis' : Disjoint R D := hdis.mono_right (subset_insert _ _)
    have haRD : a∉R∪D := by simp [haR,ha]
    have heq : R∪insert a D=insert a (R∪D) := by ext x;simp
    rw [heq,sum_powerset_insert haRD]
    have hzero : (∑ S∈(R∪D).powerset,
        mass (insert a (R∪D)) p S*g (S∩R))=
        (1-p)*(∑ S∈(R∪D).powerset,mass (R∪D) p S*g (S∩R)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S hS
      rw [mass_insert_absent _ _ _ haRD (mem_powerset.mp hS)]
      ring
    have hone : (∑ S∈(R∪D).powerset,
        mass (insert a (R∪D)) p (insert a S)*g (insert a S∩R))=
        p*(∑ S∈(R∪D).powerset,mass (R∪D) p S*g (S∩R)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S hS
      have hi : insert a S∩R=S∩R := by ext x;by_cases hx : x=a <;> simp [hx,haR]
      rw [mass_insert_present _ _ _ haRD (mem_powerset.mp hS),hi]
      ring
    rw [hzero,hone,ih hdis']
    ring

/-- Restricting the final random sample to a real prefix gives its original
Bernoulli law. No independence assertion is supplied as a premise. -/
theorem sum_mass_restrict (U R : Finset α) (p : ℝ) (g : Finset α → ℝ)
    (hR : R⊆U) :
    (∑ S∈U.powerset,mass U p S*g (S∩R))=
      ∑ A∈R.powerset,mass R p A*g A := by
  have h := sum_mass_restrict_union R (U\R) p g disjoint_sdiff_self_right
  simpa only [union_sdiff_of_subset hR] using h

/-- A fresh selected edge is independent of the actual earlier-edge sample.
This exact identity is the probabilistic input for sampled-output lightness. -/
theorem sum_mass_mem_restrict (U R : Finset α) (p : ℝ) (g : Finset α → ℝ)
    {e : α} (hR : R⊆U) (heU : e∈U) (heR : e∉R) :
    (∑ S∈U.powerset,mass U p S*(if e∈S then g (S∩R) else 0))=
      p*(∑ A∈R.powerset,mass R p A*g A) := by
  classical
  have h := sum_mass_restrict U (insert e R) p
    (fun A => if e∈A then g (A∩R) else 0) (insert_subset heU hR)
  have hi (S : Finset α) : S∩insert e R∩R=S∩R := by ext x;simp;tauto
  simp only [mem_inter,mem_insert_self,and_true,hi] at h
  rw [h,sum_powerset_insert heR]
  have hz : (∑ A∈R.powerset,mass (insert e R) p A*(if e∈A then g (A∩R) else 0))=0 := by
    apply sum_eq_zero
    intro A hA
    have heA : e∉A := fun he => heR (mem_powerset.mp hA he)
    simp [heA]
  rw [hz,zero_add,mul_sum]
  apply sum_congr rfl
  intro A hA
  have hAR := mem_powerset.mp hA
  have hiA : insert e A∩R=A := by ext x;simp;constructor <;> aesop
  rw [mass_insert_present _ _ _ heR hAR,hiA]
  simp only [mem_insert_self,ite_true]
  ring
end LightSpanners.FiniteSampling
