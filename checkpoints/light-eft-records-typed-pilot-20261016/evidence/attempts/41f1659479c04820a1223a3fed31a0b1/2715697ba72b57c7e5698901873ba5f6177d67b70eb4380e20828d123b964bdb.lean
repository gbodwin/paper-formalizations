import LightEFTSpanners.StoredCandidateBankRepresentation

namespace LightEFTSpanners.StoredForestCandidates
open SimpleGraph
attribute [local instance] Classical.propDecidable

theorem pairList_sorted {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ) :
    (pairList G.edgeFinset.toList).mergeSort (fun x y => decide (w s(y.1,y.2)≤w s(x.1,x.2)))=
      pairList (LightSpanners.greedyInput G (fun e => (w e:ℝ))) := by
  unfold pairList LightSpanners.greedyInput
  symm
  apply List.map_mergeSort
  intro a _ b _
  have ha : s(a.out.1,a.out.2)=a := a.out_eq
  have hb : s(b.out.1,b.out.2)=b := b.out_eq
  simp [ha,hb]

theorem pairList_filtered {n : ℕ} (Q : SimpleGraph (Fin n)) (es : List (Sym2 (Fin n))) :
    ((pairList es).filter fun x => decide (s(x.1,x.2)∉StoredSample.edgeSet (graphEdges Q)))=
      pairList (es.filter fun e => decide (e∉Q.edgeFinset)) := by
  unfold pairList
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  have he : s(e.out.1,e.out.2)=e := e.out_eq
  change decide (s(e.out.1,e.out.2)∉StoredSample.edgeSet (graphEdges Q))=decide (e∉Q.edgeFinset)
  rw [graphEdges_edgeSet,he]
end LightEFTSpanners.StoredForestCandidates

namespace LightEFTSpanners.StoredSortedCandidateInput
open StoredForestCandidates
attribute [local instance] Classical.propDecidable

theorem execute_original_order {n : ℕ} (G Q : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (banks : Sym2 (Fin n) → StoredDrawLookup.TypedBank n) :
    execute (StoredOriginalWeightLookup.encode (StoredOriginalWeightLookup.originalBank w))
      (StoredEdges.encode (graphEdges Q)) (StoredCandidateDrawLookup.encode (StoredCandidateDrawLookup.originalBank banks))
      (StoredEdges.encode (pairList G.edgeFinset.toList))=
      (rawInputs banks (pairList (LightEFTSpanners.input G Q (fun e => (w e:ℝ)))).reverse).map StoredForestBank.encode := by
  have hw (e : Sym2 (Fin n)) : StoredOriginalWeightLookup.weight e (StoredOriginalWeightLookup.originalBank w)=w e :=
    congrFun (StoredOriginalWeightLookup.originalBank_represents w) e
  have hb (e : Sym2 (Fin n)) : StoredCandidateDrawLookup.typedValue e (StoredCandidateDrawLookup.originalBank banks)=banks e :=
    congrFun (StoredCandidateDrawLookup.originalBank_represents banks) e
  rw [execute_encoded]
  simp only [hw]
  rw [pairList_sorted,StoredOriginalCandidateRecords.typedValue_filter,pairList_filtered]
  simp only [hb]
  simp only [rawInputs,LightEFTSpanners.input,List.map_reverse]
end LightEFTSpanners.StoredSortedCandidateInput
