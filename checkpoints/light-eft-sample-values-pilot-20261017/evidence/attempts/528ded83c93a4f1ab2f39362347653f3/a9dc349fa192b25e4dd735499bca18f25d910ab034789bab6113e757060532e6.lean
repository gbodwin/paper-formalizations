import LightEFTSpanners.StoredPreparedCandidateOriginal
import LightEFTSpanners.StoredAssignmentExecutable

namespace LightEFTSpanners.StoredPreparedCandidates
open StoredCandidatePreparation
open StoredPreparedHostVote (catalogue eligibleIndex)

def indexedRecords {n : ℕ} {J : Type*} (id : J → ℕ)
    (incidence : J → List (Fin n × Fin n))
    (input : Sym2 (Fin n) → J → StoredHosts.TypedInput n)
    (js : List J) (es : List (Fin n × Fin n)) : List (TypedInput n) :=
  es.map fun e => ⟨e,catalogue id incidence (input s(e.1,e.2)) js⟩

def selectedIndices {n : ℕ} {J : Type*}
    (incidence : J → List (Fin n × Fin n)) (js : List J) (e : Sym2 (Fin n)) : List J :=
  js.filter fun j => decide (e∈StoredSample.edgeSet (incidence j))

theorem indexed_eq_assignment {n : ℕ} {J : Type*}
    (w : Sym2 (Fin n) → ℚ) (t : ℚ) (id : J → ℕ)
    (incidence : J → List (Fin n × Fin n))
    (input : Sym2 (Fin n) → J → StoredHosts.TypedInput n)
    (js : List J) (es : List (Fin n × Fin n)) :
    (indexedRecords id incidence input js es).map (typedResult w t)=
      StoredCandidates.assignmentRecords w t (selectedIndices incidence js) input es := by
  simp only [indexedRecords,List.map_map,Function.comp_def,StoredCandidates.assignmentRecords]
  congr 1
  funext e
  simp only [typedResult,StoredPreparedHostVote.chosen_catalogue,selectedIndices]
  rfl

/-- Static original incidence and assignment representations suffice. The
actual machine builds all candidate budgets and selected host lists itself. -/
theorem execute_assignment {n m : ℕ} {J : Type*} [DecidableEq J]
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e)
    (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (a : SampledGreedy.Assignment (Fin n) J m)
    (h : ℕ) (id : J → ℕ) (incidence : J → List (Fin n × Fin n))
    (input : Sym2 (Fin n) → J → StoredHosts.TypedInput n)
    (js : List J) (es : List (Fin n × Fin n)) (hj : js.Nodup)
    (cover : ∀ e∈es,∀ j∈eligible s(e.1,e.2),j∈js)
    (inc : ∀ e∈es,∀ j∈js,j∈eligible s(e.1,e.2) ↔ s(e.1,e.2)∈StoredSample.edgeSet (incidence j))
    (hh : ∀ e∈es,∀ j∈js,host j=StoredSample.edgeSet (input s(e.1,e.2) j).edges)
    (hd : ∀ e∈es,∀ j∈js,
      ((input s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j)) :
    ∃ out : List (Fin n × Fin n),
      execute (StoredEdges.encode Q) (StoredEdges.encode Q) (StoredRecords.encodeWeights w)
        n h t ((indexedRecords id incidence input js es).map encode)=StoredEdges.encode out ∧
      StoredSample.edgeSet out=SampledGreedy.edges (StoredSample.edgeSet Q)
        (fun d => (w d:ℝ)) (t:ℝ) eligible host (SampledGreedy.assignmentTape a) h
        (es.map fun e => s(e.1,e.2)).reverse := by
  have he : ∀ e∈es,(selectedIndices incidence js s(e.1,e.2)).toFinset=eligible s(e.1,e.2) := by
    intro e hem
    ext j
    simp only [selectedIndices,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨hm,hi⟩
      exact (inc e hem j hm).mpr hi
    · intro hi
      exact ⟨cover e hem j hi,(inc e hem j (cover e hem j hi)).mp hi⟩
  have hs := StoredCandidates.assignment_schedule Q Q w t eligible host a h
    (selectedIndices incidence js) input es (fun _ _ => hj.filter _) he
    (fun e hem j hjm => hh e hem j (List.mem_of_mem_filter hjm))
    (fun e hem j hjm => hd e hem j (List.mem_of_mem_filter hjm))
  rw [←indexed_eq_assignment w t id incidence input js es] at hs
  simpa only [indexedRecords,List.map_map,Function.comp_def] using
    execute_original Q w hw t eligible host (SampledGreedy.assignmentTape a) h
      (indexedRecords id incidence input js es) hs
end LightEFTSpanners.StoredPreparedCandidates
