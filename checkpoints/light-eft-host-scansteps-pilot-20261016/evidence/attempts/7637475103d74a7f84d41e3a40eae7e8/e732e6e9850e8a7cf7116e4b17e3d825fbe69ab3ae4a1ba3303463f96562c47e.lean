import LightEFTSpanners.StoredPreparedCandidateAssignment
import LightEFTSpanners.StoredOutputLaw

namespace LightEFTSpanners.StoredPreparedCandidates
open StoredCandidatePreparation
open StoredCandidates (OutputSatisfies)

theorem assignment_failure_le {n m : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n))) (h : ℕ)
    (id : J → ℕ) (incidence : J → List (Fin n × Fin n))
    (input : SampledGreedy.Assignment (Fin n) J m → Sym2 (Fin n) → J → StoredHosts.TypedInput n)
    (js : List J) (es : List (Fin n × Fin n)) (hj : js.Nodup)
    (cover : ∀ e∈es,∀ j∈eligible s(e.1,e.2),j∈js)
    (inc : ∀ e∈es,∀ j∈js,j∈eligible s(e.1,e.2) ↔ s(e.1,e.2)∈StoredSample.edgeSet (incidence j))
    (hh : ∀ a,∀ e∈es,∀ j∈js,host j=StoredSample.edgeSet (input a s(e.1,e.2) j).edges)
    (hd : ∀ a,∀ e∈es,∀ j∈js,
      ((input a s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j))
    (law : FiniteProbability.Law (SampledGreedy.Assignment (Fin n) J m))
    (P : Finset (Sym2 (Fin n)) → Prop) :
    law.prob (fun a => ¬OutputSatisfies n P
      (execute (StoredEdges.encode Q) (StoredEdges.encode Q) (StoredRecords.encodeWeights w)
        n h t ((indexedRecords id incidence (input a) js es).map encode))) ≤
    law.prob (fun a => ¬P (SampledGreedy.edges (StoredSample.edgeSet Q)
      (fun d => (w d:ℝ)) (t:ℝ) eligible host (SampledGreedy.assignmentTape a) h
      (es.map fun e => s(e.1,e.2)).reverse)) := by
  apply FiniteProbability.Law.prob_mono
  intro a hbad hgood
  obtain ⟨out,run,edges⟩ := execute_assignment Q w hw t eligible host a h id incidence
    (input a) js es hj cover inc (hh a) (hd a)
  exact hbad ⟨out,run,edges.symm ▸ hgood⟩
end LightEFTSpanners.StoredPreparedCandidates
