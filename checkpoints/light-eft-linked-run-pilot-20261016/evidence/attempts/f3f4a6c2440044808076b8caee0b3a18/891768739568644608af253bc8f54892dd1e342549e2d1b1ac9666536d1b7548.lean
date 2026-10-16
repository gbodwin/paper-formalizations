import LightEFTSpanners.StoredForestHostSize
import LightEFTSpanners.StoredCandidateBound

namespace LightEFTSpanners.StoredForestBank

def hostBound {n : ℕ} (q m : ℕ) (fs : List (List (Fin n × Fin n)))
    (bank : StoredDrawLookup.TypedBank n) : ℕ :=
  drawCount bank*(n*n*(q+m+edgeCount fs+11)+4*n+SampleVote.perSample n+5)+n*n*drawCells bank+4

theorem host_cap_le {n : ℕ} (q m : ℕ) (fs : List (List (Fin n × Fin n)))
    (bank : StoredDrawLookup.TypedBank n) (i : ℕ) (r : StoredComponentRecord.TypedInput n)
    (hr : r∈StoredForestInput.typedInputs bank i fs) :
    StoredCandidates.hostCap q m r.host ≤ hostBound q m fs bank := by
  obtain ⟨he,hd,hc⟩ := input_host_size fs bank i r hr
  unfold StoredCandidates.hostCap hostBound
  gcongr

theorem candidate_cap_le {n : ℕ} (q m : ℕ) (fs : List (List (Fin n × Fin n)))
    (w : Sym2 (Fin n) → ℚ) (t : ℚ) (r : TypedInput n) :
    StoredCandidates.candidateCap q m (StoredForestCandidate.typedResult fs r.bank r.edge w t) ≤
      fs.length*n*(hostBound q m fs r.bank+2)+3 := by
  let cs := StoredForestInput.typedInputs r.bank 0 fs
  let eligible := (cs.map StoredComponentRecord.typedResult).filter
    (StoredHostPreparation.eligible r.edge.1 r.edge.2)
  have hl : eligible.length ≤ fs.length*n :=
    (List.length_filter_le _ _).trans (by simpa [cs] using typed_inputs_length fs r.bank 0)
  have hevery : ∀ x∈eligible, StoredCandidates.hostCap q m x.host+2 ≤ hostBound q m fs r.bank+2 := by
    intro x hx
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_filter.mp hx).1
    exact Nat.add_le_add_right (host_cap_le q m fs r.bank 0 c hc) 2
  have sum_bound : ∀ xs : List (StoredHostPreparation.TypedRecord n),
      (∀ x∈xs, StoredCandidates.hostCap q m x.host+2 ≤ hostBound q m fs r.bank+2) →
      (xs.map fun x => StoredCandidates.hostCap q m x.host+2).sum ≤
        xs.length*(hostBound q m fs r.bank+2) := by
    intro xs
    induction xs with
    | nil => intro _;simp
    | cons a xs ih =>
      intro hall
      have ha := hall a (by simp)
      have ht := ih (fun x hx => hall x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hs := sum_bound eligible hevery
  simp only [StoredCandidates.candidateCap,StoredForestCandidate.typedResult,
    StoredCandidatePreparation.typedResult,StoredComponentCandidate.typedPrepared,
    List.map_map,Function.comp_def]
  exact Nat.add_le_add_right (hs.trans (Nat.mul_le_mul_right _ hl)) 3
end LightEFTSpanners.StoredForestBank
