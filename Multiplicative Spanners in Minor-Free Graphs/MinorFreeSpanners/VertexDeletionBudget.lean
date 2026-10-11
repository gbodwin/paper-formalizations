import MinorFreeSpanners.MinorSingletonDegree
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Actual induced vertex deletion loses no more than the sum of original
incident degrees at deleted vertices. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Count all lost original simple edges through their actual deleted
endpoints; double counting only enlarges the upper bound. -/
theorem induced_vertex_deletion_edge_budget (G : SimpleGraph V) (S : Finset V) :
    G.edgeFinset.card ≤ (G.induce (S:Set V)).edgeFinset.card+
      ∑ x ∈ Finset.univ \ S, G.degree x := by
  classical
  let kept := G.edgeFinset ∩ S.sym2
  let lost := (Finset.univ \ S).biUnion (fun x => G.incidenceFinset x)
  have hcover : G.edgeFinset ⊆ kept ∪ lost := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
      by_cases hx : x ∈ S
      · by_cases hy : y ∈ S
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he,by simp [hx,hy]⟩)
        · apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          refine ⟨y,by simp [hy],?_⟩
          rw [G.incidenceFinset_eq_filter]
          simp [he]
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨x,by simp [hx],?_⟩
        rw [G.incidenceFinset_eq_filter]
        simp [he]
  have hk : kept.card=(G.induce (S:Set V)).edgeFinset.card := by
    have h := congrArg Finset.card (G.map_edgeFinset_induce (s:=(S:Set V)))
    simpa only [Finset.card_map,Finset.toFinset_coe,kept,SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using h.symm
  have hl : lost.card ≤ ∑ x ∈ Finset.univ \ S, G.degree x := by
    have h := Finset.card_biUnion_le (s:=Finset.univ \ S) (t:=fun x => G.incidenceFinset x)
    simpa only [card_incidenceFinset_eq_degree,lost] using h
  calc
    _ ≤ (kept ∪ lost).card := Finset.card_le_card hcover
    _ ≤ kept.card+lost.card := Finset.card_union_le _ _
    _ ≤ _ := by omega

end MinorFreeSpanners
