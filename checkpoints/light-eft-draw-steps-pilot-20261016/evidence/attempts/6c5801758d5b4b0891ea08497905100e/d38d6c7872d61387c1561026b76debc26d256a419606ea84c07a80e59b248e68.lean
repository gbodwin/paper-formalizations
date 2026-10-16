import LightEFTSpanners.MultigraphFaultConnectivity
import Mathlib.Tactic

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Integer cardinality of the native cut. Every parallel edge keeps its
own identity and a loop contributes zero. -/
noncomputable def cutSize (G : Graph V E) (S : Set V) : ℤ :=
  (G.edgeCut S).toFinset.card

theorem cutSize_sum (G : Graph V E) (S : Set V) :
    cutSize G S=∑ e : E,if e∈G.edgeCut S then (1:ℤ) else 0 := by
  simp [cutSize]

theorem cutSize_nonneg (G : Graph V E) (S : Set V) : 0≤cutSize G S := by
  unfold cutSize
  positivity

theorem cutSize_compl (G : Graph V E) (S : Set V) : cutSize G Sᶜ=cutSize G S := by
  rw [cutSize_sum,cutSize_sum]
  apply sum_congr rfl
  intro e _
  by_cases he : e∈G.edgeSet
  · obtain ⟨a,b,h⟩ := Graph.exists_isLink_of_mem_edgeSet he
    simp only [h.mem_edgeCut_iff,Set.mem_compl_iff,not_not]
    congr 1
    apply propext
    tauto
  · have hn : e∉G.edgeCut S := fun h => he (Graph.edgeCut_subset_edgeSet h)
    have hn' : e∉G.edgeCut Sᶜ := fun h => he (Graph.edgeCut_subset_edgeSet h)
    simp [hn,hn']

/-- The native finite cut function is submodular; this is proved edge by
edge and is valid for loops, parallel edges, and unused ambient edge IDs. -/
theorem cutSize_submodular (G : Graph V E) (S T : Set V) :
    cutSize G (S∩T)+cutSize G (S∪T)≤cutSize G S+cutSize G T := by
  simp only [cutSize_sum,←sum_add_distrib]
  apply sum_le_sum
  intro e _
  by_cases he : e∈G.edgeSet
  · obtain ⟨a,b,h⟩ := Graph.exists_isLink_of_mem_edgeSet he
    simp only [h.mem_edgeCut_iff,Set.mem_inter_iff,Set.mem_union]
    by_cases has : a∈S <;> by_cases hat : a∈T <;>
      by_cases hbs : b∈S <;> by_cases hbt : b∈T <;> simp [has,hat,hbs,hbt]
  · have hn (A : Set V) : e∉G.edgeCut A := fun h => he (Graph.edgeCut_subset_edgeSet h)
    simp only [hn,ite_false,add_zero,le_refl]

/-- Symmetric native cuts also satisfy difference uncrossing. -/
theorem cutSize_posimodular (G : Graph V E) (S T : Set V) :
    cutSize G (S\T)+cutSize G (T\S)≤cutSize G S+cutSize G T := by
  have h := cutSize_submodular G S Tᶜ
  have h₁ : S∩Tᶜ=S\T := rfl
  have h₂ : S∪Tᶜ=(T\S)ᶜ := by ext x; simp; tauto
  simpa only [h₁,h₂,cutSize_compl] using h
end LightEFTSpanners.MultigraphCuts
