import MinorFreeSpanners.ResidualComponents

namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Every actual residual component is smaller than a core and has a real
edge to a selected core. Connectedness is required of the original host. -/
theorem core_residual_boundary {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (k : ℕ) (hkN : k ≤ Fintype.card V)
    (P : Finset (Finset V))
    (hmax : ∀ T : Finset V, ConnectedWithin G T →
      Disjoint T (P.biUnion id) → T.card < k)
    (c : (G.induce (↑((P.biUnion id)ᶜ : Finset V) : Set V)).ConnectedComponent) :
    (ResidualComponents.block G (P.biUnion id)ᶜ c).card < k ∧
    ∃ S∈P, ∃ x∈ResidualComponents.block G (P.biUnion id)ᶜ c,
      ∃ y∈S, G.Adj x y := by
  classical
  let U := P.biUnion id
  let R := Uᶜ
  let W := ResidualComponents.block G R c
  have hW : ConnectedWithin G W := ResidualComponents.connected G R c
  have hdis : Disjoint W U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    have hr := ResidualComponents.subset G R c hv
    exact (Finset.mem_compl.mp hr) hu
  have hsmall : W.card < k := hmax W hW hdis
  refine ⟨hsmall,?_⟩
  have hall : ConnectedWithin G (Finset.univ : Finset V) := by
    intro x _ y _
    obtain ⟨p⟩ := hG.preconnected x y
    exact ⟨p,by simp⟩
  obtain ⟨x,hx,y,_,hy,hxy⟩ := hall.boundary (Finset.subset_univ W)
    (ResidualComponents.nonempty G R c) (by simp;omega)
  have hyU : y∈U := by
    by_contra hn
    have hyR : y∈R := Finset.mem_compl.mpr hn
    exact hy (ResidualComponents.closed_adj G R c hx hyR hxy)
  obtain ⟨S,hS,hyS⟩ := Finset.mem_biUnion.mp hyU
  exact ⟨S,hS,x,hx,y,hyS,hxy⟩

end MinorFreeSpanners
