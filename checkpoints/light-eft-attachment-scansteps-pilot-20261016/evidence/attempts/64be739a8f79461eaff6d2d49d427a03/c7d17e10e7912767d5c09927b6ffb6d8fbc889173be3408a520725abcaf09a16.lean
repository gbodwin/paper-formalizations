import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace LightEFTSpanners.EvenSplitting
open Finset
variable {V I : Type*} [DecidableEq V] [Fintype I]

/-- Integral mass of the original incident edge identities whose other
endpoint lies in S. Parallel incident edges are counted separately. -/
def mass (ends : I → V) (S : Finset V) : ℤ :=
  ∑ i : I,if ends i∈S then 1 else 0

theorem mass_nonneg (ends : I → V) (S : Finset V) : 0≤mass ends S := by
  unfold mass
  exact sum_nonneg (fun i _ => by split_ifs <;> omega)

theorem mass_mono (ends : I → V) {S T : Finset V} (h : S⊆T) :
    mass ends S≤mass ends T := by
  unfold mass
  apply sum_le_sum
  intro i _
  by_cases hs : ends i∈S
  · simp [hs,h hs]
  · by_cases ht : ends i∈T <;> simp [hs,ht]

theorem mass_pos_of_mem (ends : I → V) {S : Finset V} (i : I) (hi : ends i∈S) :
    1≤mass ends S := by
  unfold mass
  have h := single_le_sum (f:=fun j : I => if ends j∈S then (1:ℤ) else 0)
    (fun j (_ : j∈(univ:Finset I)) => by split_ifs <;> omega) (mem_univ i)
  simpa only [hi,ite_true] using h

theorem mass_union_inter (ends : I → V) (S T : Finset V) :
    mass ends S+mass ends T=mass ends (S∩T)+mass ends (S∪T) := by
  simp only [mass,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hs : ends i∈S <;> by_cases ht : ends i∈T <;> simp [hs,ht]

theorem mass_sdiff_identity (ends : I → V) (S T : Finset V) :
    mass ends S+mass ends T=
      mass ends (S\T)+mass ends (T\S)+2*mass ends (S∩T) := by
  simp only [mass,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hs : ends i∈S <;> by_cases ht : ends i∈T <;> simp [hs,ht]

theorem mass_compl [Fintype V] (ends : I → V) (S : Finset V) :
    mass ends S+mass ends Sᶜ=Fintype.card I := by
  simp only [mass,← sum_add_distrib]
  have h : ∀ i : I,(if ends i∈S then (1:ℤ) else 0)+
      (if ends i∈Sᶜ then 1 else 0)=1 := by intro i; by_cases hi : ends i∈S <;> simp [hi]
  simp_rw [h]
  simp
end LightEFTSpanners.EvenSplitting
