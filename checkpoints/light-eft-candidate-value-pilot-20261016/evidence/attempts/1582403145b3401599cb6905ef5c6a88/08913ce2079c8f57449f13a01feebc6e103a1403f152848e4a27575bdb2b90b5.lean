import LightEFTSpanners.BernoulliFlagEncoding

namespace LightEFTSpanners.BernoulliFlags
open Finset LightSpanners.FiniteSampling FiniteProbability
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

theorem productMass_total (p : ℝ) : ∑ bits : α → Bool,productMass p bits=1 := by
  simp_rw [productMass_eq]
  have he := Equiv.sum_comp (flagEquiv (α:=α)) (fun S => mass univ p S)
  change (∑ bits : α → Bool,mass univ p (selected bits))=(∑ S : Finset α,mass univ p S) at he
  rw [he]
  have hu : (univ : Finset α).powerset=univ := by ext S;simp
  simpa only [hu] using sum_mass (univ : Finset α) p

noncomputable def law (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) : Law (α → Bool) where
  mass := productMass p
  nonneg bits := by
    unfold productMass
    apply Finset.prod_nonneg
    intro x _
    split_ifs <;> linarith
  total := productMass_total p

theorem probability_selected (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (P : Finset α → Prop) :
    (law (α:=α) p hp0 hp1).prob (fun bits => P (selected bits))=
      ∑ S : Finset α,if P S then mass univ p S else 0 := by
  unfold Law.prob law
  simp_rw [productMass_eq]
  exact Equiv.sum_comp flagEquiv (fun S => if P S then mass univ p S else 0)

end LightEFTSpanners.BernoulliFlags
