import LightEFTSpanners.NativeQuotientCardinality
import LightEFTSpanners.NativePartitionCriterion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V W E I : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The actual original crossing identities of an ambient vertex labeling. -/
noncomputable def crossingIdentities (G : Graph V E) (f : V → W) : Finset E :=
  univ.filter (fun e => ∃ u v,G.IsLink e u v ∧ f u≠f v)

/-- Ambient labels restricted to actual vertices give exactly the same
original crossing identities as the actual partition definition. -/
theorem actualPartitionCrossings_eq (G : Graph V E) (f : V → W) :
    actualPartitionCrossings G (fun a : G.vertexSet => f a)=crossingIdentities G f := by
  ext e
  simp only [actualPartitionCrossings,crossingIdentities,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,b,he,hn⟩
    exact ⟨a.val,b.val,he,hn⟩
  · rintro ⟨a,b,he,hn⟩
    exact ⟨⟨a,he.left_mem⟩,⟨b,he.right_mem⟩,he,hn⟩

theorem crossingQuotient_edgeSet (G : Graph V E) (f : V → W) :
    (crossingQuotient G f).edgeSet=(crossingIdentities G f:Set E) := by
  ext e
  constructor
  · rintro ⟨_,h⟩
    exact mem_filter.mpr ⟨mem_univ _,h⟩
  · intro he
    obtain ⟨u,v,huv,hn⟩ := (mem_filter.mp he).2
    exact ⟨(huv.map f).edge_mem,u,v,huv,hn⟩

theorem crossingQuotient_edge_card (G : Graph V E) (f : V → W) :
    Nat.card (crossingQuotient G f).edgeSet=(crossingIdentities G f).card := by
  rw [crossingQuotient_edgeSet]
  simp

/-- Restricting an actual edge color selects exactly that fiber of the original
crossing identities. Loops and parallel edges retain their intended semantics. -/
theorem crossingIdentities_color (G : Graph V E) (f : V → W) (color : E → I) (c : I) :
    crossingIdentities (G.restrict {e | color e=c}) f=
      (crossingIdentities G f).filter (fun e => color e=c) := by
  ext e
  simp only [crossingIdentities,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨u,v,⟨hc,he⟩,hn⟩
    exact ⟨⟨u,v,he,hn⟩,hc⟩
  · rintro ⟨⟨u,v,he,hn⟩,hc⟩
    exact ⟨u,v,⟨hc,he⟩,hn⟩

/-- An actual edge coloring partitions all quotient edges exactly. This is a
finite identity on original IDs, not an assumed partition of numerical counts. -/
theorem color_crossing_card_sum [Fintype I] (G : Graph V E) (f : V → W) (color : E → I) :
    (∑ c : I,Nat.card (crossingQuotient (G.restrict {e | color e=c}) f).edgeSet)=
      (crossingIdentities G f).card := by
  simp_rw [crossingQuotient_edge_card,crossingIdentities_color]
  exact (card_eq_sum_card_fiberwise (f:=color) (s:=crossingIdentities G f)
    (t:=univ) (fun _ _ => mem_univ _)).symm
end LightEFTSpanners.MultigraphCuts
