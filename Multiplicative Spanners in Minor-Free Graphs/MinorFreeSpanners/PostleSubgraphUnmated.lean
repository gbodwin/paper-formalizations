import MinorFreeSpanners.PostleMates

/-! Re-establish unmatedness after graph deletions by the proved actual
small-dense alternative, rather than an unjustified hereditary assertion. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem postle_subgraph_dense_or_unmated (G H : SimpleGraph V) (hHG : H ≤ G)
    (K d ε₁ ε₂ : ℝ) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂0 : 0 ≤ ε₂) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*K*d ∧
      ε₁*ε₂*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
      Unmated H K ε₁ ε₂ d := by
  classical
  rcases postle_small_dense_or_unmated H K d ε₁ ε₂ hK hd hε₁0 hε₁1 hε₂0 with ⟨S,hS,hE⟩ | hu
  · have hle : H.induce (S:Set V) ≤ G.induce (S:Set V) := fun _ _ h => hHG h
    have hc := Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)
    have hcR : ((H.induce (S:Set V)).edgeFinset.card:ℝ) ≤
        ((G.induce (S:Set V)).edgeFinset.card:ℝ) := by exact_mod_cast hc
    exact Or.inl ⟨S,hS,hE.trans hcR⟩
  · exact Or.inr hu

end MinorFreeSpanners
