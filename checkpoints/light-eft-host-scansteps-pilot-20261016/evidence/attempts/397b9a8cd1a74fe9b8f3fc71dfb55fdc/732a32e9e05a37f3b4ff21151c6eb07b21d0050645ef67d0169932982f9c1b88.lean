import LightEFTSpanners.NativeColorCrossings

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Every occupied partition of a genuinely connected native graph has at
least one fewer crossing original identity than blocks. Fibers need not be
connected: only the entire quotient is used, so no tree quotient is assumed. -/
theorem connected_partition_crossing_lower (G : Graph V E)
    (hc : G.toSimpleGraph.Connected) {m : ℕ}
    (label : G.vertexSet → Fin m) (hsurj : Function.Surjective label) :
    m-1≤(actualPartitionCrossings G label).card := by
  classical
  let a0 : G.vertexSet := Classical.choice hc.nonempty
  let f : V → Fin m := fun v => if h : v∈G.vertexSet then label ⟨v,h⟩ else label a0
  have hf (a : G.vertexSet) : f a=label a := by simp [f,a.property]
  have hverts : (crossingQuotient G f).vertexSet=Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    obtain ⟨a,ha⟩ := hsurj i
    exact ⟨a.val,a.property,(hf a).trans ha⟩
  have hn := native_connected_card_lower (crossingQuotient G f)
    (connected_crossingQuotient G f hc)
  have hcard : Nat.card (crossingQuotient G f).vertexSet=m := by
    rw [hverts]
    simp
  have hlabels : (fun a : G.vertexSet => f a)=label := funext hf
  rw [hcard,crossingQuotient_edge_card,← actualPartitionCrossings_eq,hlabels] at hn
  omega

/-- Restricting a native graph selects exactly those crossing original edge
identities that belong to the retained set. The actual vertex domain is unchanged. -/
theorem actualPartitionCrossings_restrict (G : Graph V E) (F : Set E)
    {I : Type*} (label : G.vertexSet → I) :
    actualPartitionCrossings (G.restrict F) label=
      (actualPartitionCrossings G label).filter (fun e => e∈F) := by
  ext e
  simp only [actualPartitionCrossings,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,b,⟨he,hab⟩,hn⟩
    exact ⟨⟨a,b,hab,hn⟩,he⟩
  · rintro ⟨⟨a,b,hab,hn⟩,he⟩
    exact ⟨a,b,⟨he,hab⟩,hn⟩
end LightEFTSpanners.MultigraphCuts
