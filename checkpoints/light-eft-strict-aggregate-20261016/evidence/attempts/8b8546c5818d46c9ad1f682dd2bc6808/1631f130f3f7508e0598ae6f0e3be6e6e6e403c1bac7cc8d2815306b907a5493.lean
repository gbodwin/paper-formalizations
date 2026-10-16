import LightEFTSpanners.NativeContractionInvariants

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts
variable {V E : Type*} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The complete minimal-core reduction step in a genuine basic Eulerian
instance. The core and its internal trees are constructed. Its quotient has
strictly fewer actual vertices, is Eulerian, preserves every required fault
connection, and every supplied quotient forest packing lifts to original
forests. Existence of that quotient packing remains the induction obligation. -/
theorem exists_native_basic_core_reduction (G : Graph V E) (k : ℕ)
    (hall : G.vertexSet=Set.univ) (hdeg : ∀ v,Even (nativeDegree G v))
    {u v : G.vertexSet} (hsep : ¬FaultConnected G (2*k) u v)
    (hbasic : ∀ a : G.vertexSet,∃ b : G.vertexSet,a≠b ∧ FaultConnected G (2*k) a b) :
    ∃ K : Finset V,K⊂G.vertexSet.toFinset ∧ 2≤K.card ∧
      (G.map (collapseOutside (K:Set V)ᶜ)).vertexSet=Set.univ ∧
      Fintype.card (Option {v : V // v∉K})<Fintype.card V ∧
      (∀ w,Even (nativeDegree (G.map (collapseOutside (K:Set V)ᶜ)) w)) ∧
      (∀ (x y : G.vertexSet),FaultConnected G (2*k) x y →
        FaultConnected (G.map (collapseOutside (K:Set V)ᶜ)) (2*k)
          (mapVertex G (collapseOutside (K:Set V)ᶜ) x)
          (mapVertex G (collapseOutside (K:Set V)ᶜ) y)) ∧
      ∀ (A : Fin k → Set E),
        (∀ c,A c⊆(G.map (collapseOutside (K:Set V)ᶜ)).edgeSet) →
        (∀ c e,e∈((G.map (collapseOutside (K:Set V)ᶜ)).restrict (A c)).edgeSet →
          ((G.map (collapseOutside (K:Set V)ᶜ)).restrict (A c)).IsBridge e) →
        Pairwise (fun c d => Disjoint (A c) (A d)) →
        ∃ B : Fin k → Set E,(∀ c,B c⊆G.edgeSet ∧
          ∀ e∈(G.restrict (B c)).edgeSet,(G.restrict (B c)).IsBridge e) ∧
          Pairwise (fun c d => Disjoint (B c) (B d)) ∧
          ∀ c (x y : G.vertexSet),
            EdgeSetJoins (G.map (collapseOutside (K:Set V)ᶜ)) (A c)
              (collapseOutside (K:Set V)ᶜ x.val) (collapseOutside (K:Set V)ᶜ y.val) →
            EdgeSetJoins G (B c) x.val y.val := by
  classical
  obtain ⟨K,hproper,htwo,hsmall,_,hmin⟩ := native_exists_basic_small_core G hsep hbasic
  have hne : K.Nonempty := Finset.card_pos.mp (by omega)
  have hactual : (K:Set V)⊆G.vertexSet := by
    intro x hx
    exact Set.mem_toFinset.mp (hproper.subset hx)
  obtain ⟨x,hx⟩ := hne
  have hout : ∃ v,v∉(K:Set V)ᶜ := ⟨x,by simpa using hx⟩
  refine ⟨K,hproper,htwo,native_collapse_vertexSet G hall _ hout,
    contract_core_card_lt K htwo,even_native_degrees_map G _ hdeg,?_,?_⟩
  · exact fun _ _ h => faultConnected_map G _ h
  · intro A hA hf hd
    exact expand_native_minimal_core_forests G K k ⟨x,hx⟩ hactual (Nat.le_of_lt hsmall)
      hmin A hA hf hd
end LightEFTSpanners.EvenSplitting
