import LightEFTSpanners.BernoulliTestConcentration
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace LightEFTSpanners.BernoulliFlags
open Finset LightSpanners.FiniteSampling
variable {α : Type*} [Fintype α] [DecidableEq α]

def selected (bits : α → Bool) : Finset α := univ.filter fun x => bits x

def flags (S : Finset α) (x : α) : Bool := decide (x∈S)

omit [DecidableEq α] in
@[simp] theorem mem_selected (bits : α → Bool) (x : α) : x∈selected bits ↔ bits x=true := by
  simp [selected]

@[simp] theorem selected_flags (S : Finset α) : selected (flags S)=S := by
  ext x
  simp [flags]

@[simp] theorem flags_selected (bits : α → Bool) : flags (selected bits)=bits := by
  funext x
  simp [flags]

def flagEquiv : (α → Bool) ≃ Finset α :=
  ⟨selected,flags,flags_selected,selected_flags⟩

noncomputable def productMass (p : ℝ) (bits : α → Bool) : ℝ :=
  ∏ x,if bits x then p else 1-p

theorem productMass_eq (p : ℝ) (bits : α → Bool) :
    productMass p bits=mass univ p (selected bits) := by
  unfold productMass
  rw [Finset.prod_ite]
  have h : (univ.filter fun x => ¬bits x=true)=(univ\selected bits) := by
    ext x
    simp
  simp only [h,Finset.prod_const]
  rfl
end LightEFTSpanners.BernoulliFlags
