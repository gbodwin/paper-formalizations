import LightEFTSpanners.StoredOriginalGraphCaller

namespace LightEFTSpanners.StoredOriginalGraphCaller
open Controller

def prepared {n : ℕ} (weights : StoredOriginalWeightLookup.TypedBank n) (Q : List (Fin n × Fin n))
    (bank : StoredCandidateDrawLookup.TypedBank n) (xs : List (Fin n × Fin n)) : List (StoredForestBank.TypedInput n) :=
  (StoredOriginalCandidateRecords.typedValue Q bank (xs.mergeSort (fun x y => decide
    (StoredOriginalWeightLookup.weight s(y.1,y.2) weights≤StoredOriginalWeightLookup.weight s(x.1,x.2) weights)))).reverse

theorem full_trace {n : ℕ} (h : ℕ) (fs : List (List (Fin n × Fin n))) (Q E xs : List (Fin n × Fin n))
    (weights : StoredOriginalWeightLookup.TypedBank n) (bank : StoredCandidateDrawLookup.TypedBank n) (t : ℚ) :
    ∃ k,k≤bound n (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode xs)
      (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank) ∧
      Trace (transition n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
        (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank) t) k
        (.prepare (.sorting (.sort (StoredEdges.encode xs) [])))
        (.run ((prepared weights Q bank xs).map StoredForestBank.encode)
          (.candidates (StoredRecords.encodeWeights (fun e => StoredOriginalWeightLookup.weight e weights))
            (.select (.halt (StoredEdges.encode (StoredCandidates.selected Q
              (fun e => StoredOriginalWeightLookup.weight e weights) h
              (StoredForestBank.typedValue fs (fun e => StoredOriginalWeightLookup.weight e weights) t
                (prepared weights Q bank xs)) E)))))) := by
  let rs := prepared weights Q bank xs
  have hp := StoredSortedCandidateInput.execute_encoded weights Q bank xs
  change StoredSortedCandidateInput.execute _ _ _ _=rs.map StoredForestBank.encode at hp
  obtain ⟨a,ha,ht⟩ := StoredSortedCandidateInput.full_trace (StoredOriginalWeightLookup.encode weights)
    (StoredEdges.encode Q) (StoredCandidateDrawLookup.encode bank) (StoredEdges.encode xs)
  have hv := hp
  rw [StoredSortedCandidateInput.execute_eq] at hv
  rw [hv] at ht
  have ht := prepare_lift n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank) t ht
  have e := Trace.one (show transition n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank) t
    (.prepare (.records (.halt (rs.map StoredForestBank.encode))))=
    some (.run (rs.map StoredForestBank.encode) (.weights (.rows 0 n []))) from rfl)
  obtain ⟨b,W,hb,hW,hu⟩ := StoredWeightedForestCandidates.full_trace h fs Q E weights t rs
  rw [hW] at hu
  have hu := run_lift n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank) t
    (rs.map StoredForestBank.encode) hu
  have budget := StoredSortedCandidateInput.prepared_bound n (fs.map StoredEdges.encode)
    (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode xs)
    (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank)
  rw [hp] at budget
  refine ⟨a+(1+b),?_,ht.trans (e.trans hu)⟩
  unfold bound StoredWeightedForestCandidates.bound at *
  omega
end LightEFTSpanners.StoredOriginalGraphCaller
