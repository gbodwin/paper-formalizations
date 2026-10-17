import LightEFTSpanners.StoredAssignmentExecutable
import LightEFTSpanners.FiniteLaw

namespace LightEFTSpanners.StoredCandidates

/-- A property of the actual returned endpoint list, via its typed edge-set
representation. This is a semantic relation, not an uncharged decoder call. -/
def OutputSatisfies (n : ℕ) (P : Finset (Sym2 (Fin n)) → Prop)
    (raw : List StoredEdges.Edge) : Prop :=
  ∃ out : List (Fin n × Fin n),raw=StoredEdges.encode out ∧ P (StoredSample.edgeSet out)

theorem assignment_failure_le {n m : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n))) (h : ℕ)
    (js : Sym2 (Fin n) → List J)
    (input : SampledGreedy.Assignment (Fin n) J m → Sym2 (Fin n) → J → StoredHosts.TypedInput n)
    (es : List (Fin n × Fin n))
    (hj : ∀ e∈es,(js s(e.1,e.2)).Nodup)
    (he : ∀ e∈es,(js s(e.1,e.2)).toFinset=eligible s(e.1,e.2))
    (hh : ∀ a,∀ e∈es,∀ j∈js s(e.1,e.2),host j=StoredSample.edgeSet (input a s(e.1,e.2) j).edges)
    (hd : ∀ a,∀ e∈es,∀ j∈js s(e.1,e.2),
      ((input a s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j))
    (law : FiniteProbability.Law (SampledGreedy.Assignment (Fin n) J m))
    (P : Finset (Sym2 (Fin n)) → Prop) :
    law.prob (fun a => ¬OutputSatisfies n P
      (execute (StoredEdges.encode Q) (StoredEdges.encode Q) (StoredRecords.encodeWeights w)
        n h ((assignmentRecords w t js (input a) es).map encode))) ≤
    law.prob (fun a => ¬P (SampledGreedy.edges (StoredSample.edgeSet Q)
      (fun d => (w d:ℝ)) (t:ℝ) eligible host (SampledGreedy.assignmentTape a) h
      (es.map fun e => s(e.1,e.2)).reverse)) := by
  apply FiniteProbability.Law.prob_mono
  intro a hbad hgood
  obtain ⟨out,run,edges⟩ := execute_assignment Q w hw t eligible host a h js (input a) es hj he (hh a) (hd a)
  exact hbad ⟨out,run,edges.symm ▸ hgood⟩
end LightEFTSpanners.StoredCandidates
