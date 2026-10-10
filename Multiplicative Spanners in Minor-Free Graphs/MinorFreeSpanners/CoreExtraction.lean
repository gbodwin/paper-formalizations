import MinorFreeSpanners.ExactSizeLowerBound

namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Deleting edges preserves the actual cycle-girth lower bound. -/
theorem GirthAbove.mono {G H : SimpleGraph V} {k : ℕ}
    (hG : GirthAbove G k) (hHG : H ≤ G) : GirthAbove H k :=
  hG.of_embedding ⟨id,fun h => hHG h⟩ (fun _ _ h => h)

/-- Any desired edge count up to the original count is attained by a genuine
spanning subgraph, preserving girth. No graph-extraction oracle is assumed. -/
theorem exists_edge_trim (G : SimpleGraph V) (m k : ℕ)
    (hm : m ≤ G.edgeFinset.card) (hg : GirthAbove G k) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeFinset.card = m ∧ GirthAbove H k := by
  classical
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq hm
  let H := fromEdgeSet (S : Set (Sym2 V))
  have hHG : H ≤ G := by
    intro u v huv
    exact (mem_edgeSet G).mp (mem_edgeFinset.mp (hS huv.1))
  have hE : H.edgeFinset = S := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v =>
      simp only [mem_edgeFinset,mem_edgeSet,H,fromEdgeSet_adj]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h,((mem_edgeSet G).mp (mem_edgeFinset.mp (hS h))).ne⟩
  refine ⟨H,hHG,?_,hg.mono hHG⟩
  convert (congrArg Finset.card hE).trans hcard using 1
  congr 1
  ext e
  simp only [mem_edgeFinset]

end MinorFreeSpanners
