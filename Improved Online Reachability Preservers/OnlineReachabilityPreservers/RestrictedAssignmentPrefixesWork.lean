import OnlineReachabilityPreservers.AssignmentListRestrictedWork
import OnlineReachabilityPreservers.AssignmentPrefixesWork

/-! Exact source-level prefix bounds for both endpoint promises of Theorem 5. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

omit [LinearOrder V] [Fintype V] in
private theorem reversePath_length (p : Option (List (V × V))) :
    ((reversePath p).getD []).length = (p.getD []).length := by
  cases p <;> simp [reversePath]

/-- Known-total edge unions over all prefixes with allowed sinks. -/
theorem knownSinkAssignmentPrefixesWithWordWork_spec (G : List (V × V))
    (vertices sinks : List V) (p : ℕ) (D : List (V × V))
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (endpointSet : sinks.Nodup) :
    let n := Fintype.card V
    let out := assignmentPrefixesWithWordWork (fun _ => knownSinkPathWithWordWork G vertices sinks p) D
    (∀ A ∈ out.1, List.Nodup A) ∧ out.1.map List.toFinset = D.inits.map (plannedArcs (fun _ => knownSinkPath G.toFinset sinks.toFinset p)) ∧
      out.2 ≤ assignmentPrefixesWordBudget n D.length (knownSinkPathWordBudget n G.length sinks.length p) := by
  refine assignmentPrefixesWithWordWork_spec _ _
    (fun _ d => (knownSinkPathWithWordWork_spec G vertices sinks p d unique complete endpointSet).1) ?_ _ D ?_
  · intro _ d
    unfold knownSinkPath
    exact liftPath_length_le _ _ _
  · exact fun j => (knownSinkPathWithWordWork_spec G vertices sinks p (D.get j) unique complete endpointSet).2

/-- Known-total prefix cost including one enumeration of the indexed vertices. -/
theorem knownSinkFinAssignmentPrefixesWithWordWork_spec {n : ℕ}
    (G : List (Fin n × Fin n)) (sinks : List (Fin n)) (p : ℕ) (D : List (Fin n × Fin n))
    (endpointSet : sinks.Nodup) :
    let out := withFinVerticesWithWordWork
      (fun vertices => assignmentPrefixesWithWordWork (fun _ => knownSinkPathWithWordWork G vertices sinks p) D)
    out.1.map List.toFinset = D.inits.map (plannedArcs (fun _ => knownSinkPath G.toFinset sinks.toFinset p)) ∧
      out.2 ≤ 8*n+1+assignmentPrefixesWordBudget n D.length (knownSinkPathWordBudget n G.length sinks.length p)+4 := by
  refine withFinVerticesWithWordWork_spec
    (P := fun (lists : List (List (Fin n × Fin n))) =>
      lists.map List.toFinset = D.inits.map (plannedArcs (fun _ => knownSinkPath G.toFinset sinks.toFinset p))) _ _ ?_
  intro vertices unique complete
  simpa only [Fintype.card_fin] using
    (knownSinkAssignmentPrefixesWithWordWork_spec G vertices sinks p D unique complete endpointSet).2

/-- Arrival-index edge unions over all prefixes with allowed sinks. -/
theorem indexedSinkAssignmentPrefixesWithWordWork_spec (G : List (V × V))
    (vertices sinks : List V) (D : List (V × V))
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (endpointSet : sinks.Nodup) :
    let n := Fintype.card V
    let out := assignmentPrefixesWithWordWork (indexedSinkPathWithWordWork G vertices sinks) D
    (∀ A ∈ out.1, List.Nodup A) ∧ out.1.map List.toFinset = D.inits.map (plannedArcs (indexedSinkPath G.toFinset sinks.toFinset)) ∧
      out.2 ≤ assignmentPrefixesWordBudget n D.length (indexedSinkPathWordBudget n G.length sinks.length D.length) := by
  refine assignmentPrefixesWithWordWork_spec _ _
    (fun i d => (indexedSinkPathWithWordWork_spec G vertices sinks i d unique complete endpointSet).1) ?_ _ D ?_
  · intro _ d
    unfold indexedSinkPath
    exact liftPath_length_le _ _ _
  · intro j
    have base := (indexedSinkPathWordBudget_mono_index (Fintype.card V) G.length sinks.length) j.isLt.le
    exact (indexedSinkPathWithWordWork_spec G vertices sinks j (D.get j) unique complete endpointSet).2.trans
      base

/-- Arrival-index prefix cost including one enumeration of the indexed vertices. -/
theorem indexedSinkFinAssignmentPrefixesWithWordWork_spec {n : ℕ}
    (G : List (Fin n × Fin n)) (sinks : List (Fin n)) (D : List (Fin n × Fin n))
    (endpointSet : sinks.Nodup) :
    let out := withFinVerticesWithWordWork
      (fun vertices => assignmentPrefixesWithWordWork (indexedSinkPathWithWordWork G vertices sinks) D)
    out.1.map List.toFinset = D.inits.map (plannedArcs (indexedSinkPath G.toFinset sinks.toFinset)) ∧
      out.2 ≤ 8*n+1+assignmentPrefixesWordBudget n D.length (indexedSinkPathWordBudget n G.length sinks.length D.length)+4 := by
  refine withFinVerticesWithWordWork_spec
    (P := fun (lists : List (List (Fin n × Fin n))) =>
      lists.map List.toFinset = D.inits.map (plannedArcs (indexedSinkPath G.toFinset sinks.toFinset))) _ _ ?_
  intro vertices unique complete
  simpa only [Fintype.card_fin] using
    (indexedSinkAssignmentPrefixesWithWordWork_spec G vertices sinks D unique complete endpointSet).2

/-- Known-total edge unions over all prefixes with allowed sources. -/
theorem knownSourceAssignmentPrefixesWithWordWork_spec (G : List (V × V))
    (vertices sources : List V) (p : ℕ) (D : List (V × V))
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (endpointSet : sources.Nodup) :
    let n := Fintype.card V
    let out := assignmentPrefixesWithWordWork (fun _ => knownSourcePathWithWordWork G vertices sources p) D
    (∀ A ∈ out.1, List.Nodup A) ∧ out.1.map List.toFinset = D.inits.map (plannedArcs (fun _ => knownSourcePath G.toFinset sources.toFinset p)) ∧
      out.2 ≤ assignmentPrefixesWordBudget n D.length (knownSinkPathWordBudget n G.length sources.length p+6*G.length+14*n+12) := by
  refine assignmentPrefixesWithWordWork_spec _ _
    (fun _ d => (knownSourcePathWithWordWork_spec G vertices sources p d unique complete endpointSet).1) ?_ _ D ?_
  · intro _ d
    unfold knownSourcePath
    rw [reversePath_length]
    unfold knownSinkPath
    exact liftPath_length_le _ _ _
  · exact fun j => (knownSourcePathWithWordWork_spec G vertices sources p (D.get j) unique complete endpointSet).2

/-- Known-total prefix cost including one enumeration of the indexed vertices. -/
theorem knownSourceFinAssignmentPrefixesWithWordWork_spec {n : ℕ}
    (G : List (Fin n × Fin n)) (sources : List (Fin n)) (p : ℕ) (D : List (Fin n × Fin n))
    (endpointSet : sources.Nodup) :
    let out := withFinVerticesWithWordWork
      (fun vertices => assignmentPrefixesWithWordWork (fun _ => knownSourcePathWithWordWork G vertices sources p) D)
    out.1.map List.toFinset = D.inits.map (plannedArcs (fun _ => knownSourcePath G.toFinset sources.toFinset p)) ∧
      out.2 ≤ 8*n+1+assignmentPrefixesWordBudget n D.length (knownSinkPathWordBudget n G.length sources.length p+6*G.length+14*n+12)+4 := by
  refine withFinVerticesWithWordWork_spec
    (P := fun (lists : List (List (Fin n × Fin n))) =>
      lists.map List.toFinset = D.inits.map (plannedArcs (fun _ => knownSourcePath G.toFinset sources.toFinset p))) _ _ ?_
  intro vertices unique complete
  simpa only [Fintype.card_fin] using
    (knownSourceAssignmentPrefixesWithWordWork_spec G vertices sources p D unique complete endpointSet).2

/-- Arrival-index edge unions over all prefixes with allowed sources. -/
theorem indexedSourceAssignmentPrefixesWithWordWork_spec (G : List (V × V))
    (vertices sources : List V) (D : List (V × V))
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (endpointSet : sources.Nodup) :
    let n := Fintype.card V
    let out := assignmentPrefixesWithWordWork (indexedSourcePathWithWordWork G vertices sources) D
    (∀ A ∈ out.1, List.Nodup A) ∧ out.1.map List.toFinset = D.inits.map (plannedArcs (indexedSourcePath G.toFinset sources.toFinset)) ∧
      out.2 ≤ assignmentPrefixesWordBudget n D.length (indexedSinkPathWordBudget n G.length sources.length D.length+6*G.length+14*n+12) := by
  refine assignmentPrefixesWithWordWork_spec _ _
    (fun i d => (indexedSourcePathWithWordWork_spec G vertices sources i d unique complete endpointSet).1) ?_ _ D ?_
  · intro _ d
    unfold indexedSourcePath
    rw [reversePath_length]
    unfold indexedSinkPath
    exact liftPath_length_le _ _ _
  · intro j
    have base := (indexedSinkPathWordBudget_mono_index (Fintype.card V) G.length sources.length) j.isLt.le
    exact (indexedSourcePathWithWordWork_spec G vertices sources j (D.get j) unique complete endpointSet).2.trans
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right base _) _) _)

/-- Arrival-index prefix cost including one enumeration of the indexed vertices. -/
theorem indexedSourceFinAssignmentPrefixesWithWordWork_spec {n : ℕ}
    (G : List (Fin n × Fin n)) (sources : List (Fin n)) (D : List (Fin n × Fin n))
    (endpointSet : sources.Nodup) :
    let out := withFinVerticesWithWordWork
      (fun vertices => assignmentPrefixesWithWordWork (indexedSourcePathWithWordWork G vertices sources) D)
    out.1.map List.toFinset = D.inits.map (plannedArcs (indexedSourcePath G.toFinset sources.toFinset)) ∧
      out.2 ≤ 8*n+1+assignmentPrefixesWordBudget n D.length (indexedSinkPathWordBudget n G.length sources.length D.length+6*G.length+14*n+12)+4 := by
  refine withFinVerticesWithWordWork_spec
    (P := fun (lists : List (List (Fin n × Fin n))) =>
      lists.map List.toFinset = D.inits.map (plannedArcs (indexedSourcePath G.toFinset sources.toFinset))) _ _ ?_
  intro vertices unique complete
  simpa only [Fintype.card_fin] using
    (indexedSourceAssignmentPrefixesWithWordWork_spec G vertices sources D unique complete endpointSet).2

end OnlineReachabilityPreservers
