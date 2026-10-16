import LightEFTSpanners.StoredCandidateDrawEncoding

namespace LightEFTSpanners.StoredSortedCandidateInput
open Controller
inductive State where
  | sorting : StoredWeightSort.State → State
  | records : StoredOriginalCandidateRecords.State → State
  deriving DecidableEq, Repr

def transition (weights : StoredOriginalWeightLookup.Bank) (Q : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) : State → Option State
  | .sorting (.halt xs) => some (.records (.scan xs []))
  | .sorting st => (StoredWeightSort.transition weights st).map State.sorting
  | .records st => (StoredOriginalCandidateRecords.transition Q bank st).map State.records

def bound (weights : StoredOriginalWeightLookup.Bank) (Q : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) : ℕ :=
  StoredWeightSort.bound weights xs+2+StoredOriginalCandidateRecords.bound Q bank xs

theorem sort_lift (weights : StoredOriginalWeightLookup.Bank) (Q : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) {k : ℕ} {s u : StoredWeightSort.State}
    (ht : Trace (StoredWeightSort.transition weights) k s u) :
    Trace (transition weights Q bank) k (.sorting s) (.sorting u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredWeightSort.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.sorting) he

theorem records_lift (weights : StoredOriginalWeightLookup.Bank) (Q : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) {k : ℕ} {s u : StoredOriginalCandidateRecords.State}
    (ht : Trace (StoredOriginalCandidateRecords.transition Q bank) k s u) :
    Trace (transition weights Q bank) k (.records s) (.records u) := by
  induction ht with
  | refl => exact .refl _
  | cons he _ ih =>
    exact Trace.cons (by simpa only [transition,Option.map_some] using congrArg (Option.map State.records) he) ih

theorem full_trace (weights : StoredOriginalWeightLookup.Bank) (Q : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) :
    ∃ k,k≤bound weights Q bank xs ∧ Trace (transition weights Q bank) k (.sorting (.sort xs []))
      (.records (.halt (StoredOriginalCandidateRecords.value Q bank
        (xs.mergeSort (StoredWeightComparison.result weights))).reverse)) := by
  obtain ⟨a,ha,ht⟩ := StoredWeightSort.full_trace weights xs
  have ht := sort_lift weights Q bank ht
  have e := Trace.one (show transition weights Q bank (.sorting (.halt (xs.mergeSort (StoredWeightComparison.result weights))))=
    some (.records (.scan (xs.mergeSort (StoredWeightComparison.result weights)) [])) from rfl)
  obtain ⟨b,hb,hu⟩ := StoredOriginalCandidateRecords.scan_trace Q bank (xs.mergeSort (StoredWeightComparison.result weights)) []
  simp only [List.append_nil] at hu
  have hu := records_lift weights Q bank hu
  refine ⟨a+(1+b),?_,ht.trans (e.trans hu)⟩
  simp only [StoredOriginalCandidateRecords.bound,List.length_mergeSort] at hb
  unfold bound StoredOriginalCandidateRecords.bound
  omega
end LightEFTSpanners.StoredSortedCandidateInput
