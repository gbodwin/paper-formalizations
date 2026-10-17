import LightEFTSpanners.HostWeightTransport
import LightSpanners.TreeReduction
import LightSpanners.SubdivisionGirth

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V W : Type*} [Fintype V] [Fintype W]
attribute [local instance] Classical.propDecidable

/-- A vertex equivalence transports the actual unordered-edge weight sum. -/
theorem totalWeight_comap_equiv (e : V ≃ W) (G : SimpleGraph W) (w : Sym2 W → ℝ) :
    totalWeight (G.comap e) (fun d => w (Sym2.map e d)) = totalWeight G w := by
  classical
  change totalWeight (G.comap e.toEmbedding) (fun d => w (Sym2.map e d)) = _
  rw [← map_symm G e, totalWeight_map_embedding]
  congr 1
  funext d
  rcases d with ⟨a,b⟩
  simp

/-- Minimum spanning trees remain minimum under literal vertex reindexing. -/
theorem minimumTree_comap_equiv (e : V ≃ W) {G T : SimpleGraph W} {w : Sym2 W → ℝ}
    (hT : IsMinimumSpanningTree G T w) :
    IsMinimumSpanningTree (G.comap e) (T.comap e) (fun d => w (Sym2.map e d)) := by
  classical
  refine ⟨fun _ _ h => hT.1 h,(Iso.comap e T).isTree_iff.mpr hT.2.1,?_⟩
  intro S hSG hS
  have hsG : S.map e.toEmbedding≤G := map_le_iff_le_comap.mpr hSG
  have hsT : (S.map e.toEmbedding).IsTree := (Iso.map e S).isTree_iff.mp hS
  have hh := hT.2.2 _ hsG hsT
  rw [totalWeight_comap_equiv, totalWeight_map_embedding] at *
  exact hh

omit [Fintype V] [Fintype W] in
/-- The cycle-normalized weighted-girth predicate transports through the same
actual graph isomorphism, without a change in threshold. -/
theorem girth_comap_equiv (e : V ≃ W) {G : SimpleGraph W} {w : Sym2 W → ℝ} {g : ℝ}
    (hg : WeightedGirthAbove G w g) :
    WeightedGirthAbove (G.comap e) (fun d => w (Sym2.map e d)) g := by
  intro a p hp d hd
  let J : G.comap e →g G := SimpleGraph.Hom.comap e G
  have hh := hg (J a) (p.map J) (hp.map e.injective) (Sym2.map e d)
    (by rw [Walk.edges_map];exact List.mem_map.mpr ⟨d,hd,rfl⟩)
  rw [walkWeight_map] at hh
  exact hh

/-- Reindexing preserves the actual graph/MST weight ratio, including its total
zero-denominator convention. -/
theorem lightness_comap_equiv (e : V ≃ W) (G T : SimpleGraph W) (w : Sym2 W → ℝ) :
    lightness (G.comap e) (T.comap e) (fun d => w (Sym2.map e d)) = lightness G T w := by
  unfold lightness
  rw [totalWeight_comap_equiv,totalWeight_comap_equiv]
end LightEFTSpanners
