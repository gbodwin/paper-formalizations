import LightEFTSpanners.StoredWeightedForestCandidates

namespace LightEFTSpanners.StoredWeightedForestCandidates
open Controller

theorem full_trace {n : ℕ} (h : ℕ) (fs : List (List (Fin n × Fin n))) (Q E : List (Fin n × Fin n))
    (bank : StoredOriginalWeightLookup.TypedBank n) (t : ℚ) (rs : List (StoredForestBank.TypedInput n)) :
    ∃ k W, k ≤ bound n (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
      (StoredOriginalWeightLookup.encode bank) (rs.map StoredForestBank.encode) ∧
      W=StoredRecords.encodeWeights (fun e => StoredOriginalWeightLookup.weight e bank) ∧
      Trace (transition n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
        (StoredOriginalWeightLookup.encode bank) t (rs.map StoredForestBank.encode)) k (.weights (.rows 0 n []))
        (.candidates W (.select (.halt (StoredEdges.encode
          (StoredCandidates.selected Q (fun e => StoredOriginalWeightLookup.weight e bank) h
            (StoredForestBank.typedValue fs (fun e => StoredOriginalWeightLookup.weight e bank) t rs) E))))) := by
  let w := fun e => StoredOriginalWeightLookup.weight e bank
  obtain ⟨k,hk,ht⟩ := StoredOriginalWeightMatrix.full_trace n (StoredOriginalWeightLookup.encode bank)
  have he := StoredOriginalWeightMatrix.execute_encoded bank
  rw [StoredOriginalWeightMatrix.execute_eq] at he
  rw [he] at ht
  have a := weights_lift n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredOriginalWeightLookup.encode bank) t (rs.map StoredForestBank.encode) ht
  have b := Trace.one (show transition n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredOriginalWeightLookup.encode bank) t (rs.map StoredForestBank.encode)
    (.weights (.halt (StoredRecords.encodeWeights w)))=
    some (.candidates (StoredRecords.encodeWeights w) (.prepare (.inputs (rs.map StoredForestBank.encode) []))) from rfl)
  obtain ⟨l,hl,hu⟩ := StoredForestCandidates.full_trace fs Q E w h t rs
  have c := candidates_lift n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredOriginalWeightLookup.encode bank) t (rs.map StoredForestBank.encode) (StoredRecords.encodeWeights w) hu
  exact ⟨k+1+l,StoredRecords.encodeWeights w,by unfold bound;omega,rfl,by simpa only [Nat.add_assoc] using a.trans (b.trans c)⟩

theorem execute_encoded {n : ℕ} (h : ℕ) (fs : List (List (Fin n × Fin n))) (Q E : List (Fin n × Fin n))
    (bank : StoredOriginalWeightLookup.TypedBank n) (t : ℚ) (rs : List (StoredForestBank.TypedInput n)) :
    execute n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
      (StoredOriginalWeightLookup.encode bank) t (rs.map StoredForestBank.encode)=
      StoredEdges.encode (StoredCandidates.selected Q (fun e => StoredOriginalWeightLookup.weight e bank) h
        (StoredForestBank.typedValue fs (fun e => StoredOriginalWeightLookup.weight e bank) t rs) E) := by
  obtain ⟨k,W,hk,_,ht⟩ := full_trace h fs Q E bank t rs
  let B := bound n (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
    (StoredOriginalWeightLookup.encode bank) (rs.map StoredForestBank.encode)
  have he : B=k+(B-k) := by omega
  unfold execute
  change (match Controller.run _ B (State.weights (.rows 0 n [])) with | State.candidates _ (.select (.halt out)) => out | _ => _) = _
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredWeightedForestCandidates
