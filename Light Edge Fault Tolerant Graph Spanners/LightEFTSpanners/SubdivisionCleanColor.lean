import LightEFTSpanners.ParallelSubdivision
import LightEFTSpanners.DisjointCycleFaults

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
variable {V I : Type*} [Fintype V] [Fintype I] (C : SimpleGraph V)
attribute [local instance] Classical.propDecidable

/-- Different copy colors have genuinely disjoint edge sets. -/
theorem color_edgeFinsets_pairwise :
    (Set.univ : Set I).PairwiseDisjoint (fun j => (colorGraph C j).edgeFinset) := by
  classical
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  rcases e with ⟨a,b⟩
  exact SimpleGraph.disjoint_left.mp (colorGraph_disjoint C hij) a b
    ((mem_edgeSet _).mp (mem_edgeFinset.mp hei))
    ((mem_edgeSet _).mp (mem_edgeFinset.mp hej))

/-- Fewer than twice as many faults as colors leave a color with at most one
failed edge. This concerns actual failed graph edges, even if F has nonedges. -/
theorem exists_clean_color (F : Finset (Sym2 (Vertex (I:=I) C)))
    (hF : F.card<2*Fintype.card I) :
    ∃ j : I,(F ∩ (colorGraph C j).edgeFinset).card≤1 := by
  classical
  obtain ⟨j,_,hj⟩ := exists_at_most_one_fault univ
    (fun j => (colorGraph C j).edgeFinset) F (by simpa using color_edgeFinsets_pairwise (I:=I) C)
    (by simpa using hF)
  exact ⟨j,hj⟩

/-- Any single failure in a color can be localized to one original base edge.
All other base edges have both subdivision edges available. -/
theorem exists_bad_base_edge [Nonempty C.edgeSet]
    (F : Finset (Sym2 (Vertex (I:=I) C))) (j : I)
    (hj : (F ∩ (colorGraph C j).edgeFinset).card≤1) :
    ∃ d : C.edgeSet, ∀ e : C.edgeSet,e≠d → ∀ a : V,a∈(e:Sym2 V) →
      s(Sum.inl a,Sum.inr (e,j))∉F := by
  classical
  let A := F ∩ (colorGraph C j).edgeFinset
  have hmem (e : C.edgeSet) (a : V) (ha : a∈(e:Sym2 V))
      (hF : s(Sum.inl a,Sum.inr (e,j))∈F) :
      s(Sum.inl a,Sum.inr (e,j))∈A := by
    apply mem_inter.mpr
    refine ⟨hF,mem_edgeFinset.mpr ((mem_edgeSet _).mpr ?_)⟩
    exact ⟨ha,rfl⟩
  by_cases hA : A.Nonempty
  · obtain ⟨x,hx⟩ := hA
    obtain ⟨b,d,hxd⟩ := color_edge_has_copy C (mem_edgeFinset.mp (mem_inter.mp hx).2)
    refine ⟨d,?_⟩
    intro e hed a ha hF
    have heq : s(Sum.inl a,Sum.inr (e,j))=x :=
      (card_le_one.mp hj) _ (hmem e a ha hF) _ hx
    rw [hxd] at heq
    rcases Sym2.eq_iff.mp heq with heq | heq
    · exact hed (congrArg Prod.fst (Sum.inr.inj heq.2))
    · cases heq.1
  · refine ⟨Classical.choice inferInstance,?_⟩
    intro e _ a ha hF
    exact hA ⟨_,hmem e a ha hF⟩
end LightEFTSpanners.ParallelSubdivision
