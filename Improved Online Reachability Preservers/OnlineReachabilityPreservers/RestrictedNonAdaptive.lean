import OnlineReachabilityPreservers.EndpointBudget
import OnlineReachabilityPreservers.PathAssignments

/-! Theorem 5 for source-restricted and sink-restricted demands, on arbitrary digraphs. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def quotientRule (G : Arcs V) : PathRule V :=
  fun A d => forwardPath (condensation G) A d.1 d.2

private def quotientTargets (G : Arcs V) (S : Finset V) : Finset V := S.image (componentLabel G)

private def quotientDomain (G : Arcs V) (S : Finset V) : Arcs V :=
  univ ×ˢ quotientTargets G S

private theorem project_mem_domain (G : Arcs V) {S : Finset V} {d : V × V} (h : d.2 ∈ S) :
    projectDemand G d ∈ quotientDomain G S :=
  mem_product.mpr ⟨mem_univ _, mem_image_of_mem _ h⟩

private theorem quotientRule_valid (G : Arcs V) (S : Finset V) :
    ∀ A ⊆ condensation G, ∀ d ∈ quotientDomain G S,
      pathArcs (quotientRule G A d) ⊆ condensation G ∧
        (∀ l, quotientRule G A d = some l → Walk (condensation G) d.1 d.2 l) ∧
        (Reach (condensation G) d.1 d.2 → ∃ l, quotientRule G A d = some l) := by
  intro A hA d _
  exact ⟨forwardEdges_subset hA d, fun _ hl => (forwardPath_spec hA hl).1,
    (forwardPath_succeeds hA (condensation_dag G)).mpr⟩

private theorem quotientRule_budget (G : Arcs V) (S : Finset V) (q : ℕ)
    (T : List (V × V)) (_ : T.Nodup) (hT : ∀ d ∈ T, d ∈ quotientDomain G S)
    (hl : T.length ≤ q) :
    (runRule (quotientRule G) ∅ T).card ≤ endpointBudget (Fintype.card V) S.card q := by
  have h := forwardRun_endpointBudget (condensation_dag G) T (quotientTargets G S)
    (fun d hd => (mem_product.mp (hT d hd)).2)
  apply h.trans
  unfold endpointBudget
  have hcard : (quotientTargets G S).card ≤ S.card := card_image_le
  gcongr

/-- The sink-restricted assignment that knows the final number of demands. -/
def knownSinkPath (G : Arcs V) (S : Finset V) (p : ℕ) (d : V × V) : Option (List (V × V)) :=
  liftPath G d (knownBudgetPath (quotientRule G) (quotientDomain G S) p
    (endpointBudget (Fintype.card V) S.card p) (projectDemand G d))

/-- The sink-restricted assignment that uses just the zero-based arrival index. -/
def indexedSinkPath (G : Arcs V) (S : Finset V) (i : ℕ) (d : V × V) : Option (List (V × V)) :=
  liftPath G d (indexSensitivePath (quotientRule G) (quotientDomain G S)
    (endpointBase (Fintype.card V) S.card) (endpointBudget (Fintype.card V) S.card)
    i (projectDemand G d))

theorem knownSinkPath_valid (G : Arcs V) {S : Finset V} (p : ℕ) {d : V × V} (h : d.2 ∈ S) :
    ValidPathChoice G d (knownSinkPath G S p d) := by
  apply liftPath_valid
  obtain ⟨hw, he⟩ := knownBudgetPath_valid (quotientRule G) (condensation G) (quotientDomain G S)
    p (endpointBudget (Fintype.card V) S.card p) _ (project_mem_domain G h) (quotientRule_valid G S)
  exact ⟨fun l hl => (hw l hl).simple_of_dag (condensation_dag G), he⟩

theorem indexedSinkPath_valid (G : Arcs V) {S : Finset V} (i : ℕ) {d : V × V} (h : d.2 ∈ S) :
    ValidPathChoice G d (indexedSinkPath G S i d) := by
  apply liftPath_valid
  obtain ⟨hw, he⟩ := indexSensitivePath_valid (quotientRule G) (condensation G)
    (quotientDomain G S) (endpointBase (Fintype.card V) S.card) (endpointBudget (Fintype.card V) S.card)
    i _ (project_mem_domain G h) (quotientRule_valid G S)
  exact ⟨fun l hl => (hw l hl).simple_of_dag (condensation_dag G), he⟩

/-- Theorem 5 with known p and a sink promise. The output is the union of the
assigned simple paths and has no additional purchased edges. -/
theorem theorem5_sinks_known_p (G : Arcs V) (S : Finset V) (p : ℕ) (D : List (V × V))
    (length_le : D.length ≤ p) (hsinks : ∀ d ∈ D, d.2 ∈ S) :
    let H := plannedArcs (fun _ => knownSinkPath G S p) D
    H ⊆ G ∧ Preserves G H D ∧
      H.card ≤ 2 * Fintype.card V + 2 * endpointBudget (Fintype.card V) S.card p := by
  have hc := plannedArcs_correct G (fun _ => knownSinkPath G S p) D (fun i =>
    knownSinkPath_valid G p (hsinks _ (List.get_mem _ _)))
  refine ⟨hc.1, hc.2, ?_⟩
  cases p with
  | zero =>
    have e : D = [] := List.length_eq_zero_iff.mp (by omega)
    subst D
    simp [plannedArcs]
  | succ p =>
    let P := D.map (projectDemand G)
    let pick := knownBudgetPath (quotientRule G) (quotientDomain G S) (p + 1)
      (endpointBudget (Fintype.card V) S.card (p + 1))
    have hsub : P.toFinset ⊆ quotientDomain G S := by
      intro d hd
      obtain ⟨s, h, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
      exact project_mem_domain G (hsinks s h)
    have hcard : P.toFinset.card ≤ p + 1 := by
      apply (List.toFinset_card_le P).trans
      simpa [P] using length_le
    have hknown := theorem15_known_budget (quotientRule G) (quotientDomain G S) _ _
      (Nat.succ_pos p) (quotientRule_budget G S _) _ hsub hcard
    have hp : (plannedArcs (fun _ => pick) P).card ≤
        2 * endpointBudget (Fintype.card V) S.card (p + 1) :=
      (card_le_card (plannedArcs_constant_le pick P)).trans hknown
    exact (plannedArcs_lift_card G (fun _ => pick) D).trans (Nat.add_le_add_left hp _)

/-- Theorem 5 with an arrival index and a sink promise. The result is valid for
every prefix and the assignment has no final-length input. -/
theorem theorem5_sinks_indexed (G : Arcs V) (S : Finset V) (D : List (V × V))
    (hsinks : ∀ d ∈ D, d.2 ∈ S) :
    let H := plannedArcs (indexedSinkPath G S) D
    H ⊆ G ∧ Preserves G H D ∧
      H.card ≤ 2 * Fintype.card V + 48 * endpointBudget (Fintype.card V) S.card D.length := by
  have hc := plannedArcs_correct G (indexedSinkPath G S) D (fun i =>
    indexedSinkPath_valid G i.1 (hsinks _ (List.get_mem _ _)))
  refine ⟨hc.1, hc.2, ?_⟩
  rcases D with _ | ⟨d, ds⟩
  · simp [plannedArcs]
  · let D := d :: ds
    let n := Fintype.card V
    let σ := S.card
    have hσ : 0 < σ := card_pos.mpr ⟨d.2, hsinks d (by simp)⟩
    have hs : σ ≤ n := card_le_univ _
    let P := D.map (projectDemand G)
    have hsub : ∀ q ∈ P, q ∈ quotientDomain G S := by
      intro q hq
      obtain ⟨s, h, rfl⟩ := List.mem_map.mp hq
      exact project_mem_domain G (hsinks s h)
    let pick := indexSensitivePath (quotientRule G) (quotientDomain G S)
      (endpointBase n σ) (endpointBudget n σ)
    have hp :=
      theorem16_index_sensitive (quotientRule G) (quotientDomain G S) (endpointBase n σ)
        (endpointBudget n σ) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
        (quotientRule_budget G S) 8 3 (endpointBudget_dyadic_sum hσ hs)
        (fun _ h => endpointBudget_final_quota hσ hs h) P hsub
    change (plannedArcs pick P).card ≤ 48 * endpointBudget n σ P.length at hp
    have hp' : (plannedArcs pick P).card ≤ 48 * endpointBudget n σ D.length := by
      simpa only [show P.length = D.length by simp [P]] using hp
    exact (plannedArcs_lift_card G pick D).trans (Nat.add_le_add_left hp' _)

/-- Reversing the input and then the assigned path gives the known-p source rule. -/
def knownSourcePath (G : Arcs V) (S : Finset V) (p : ℕ) (d : V × V) : Option (List (V × V)) :=
  reversePath (knownSinkPath (reverseArcs G) S p d.swap)

/-- Reversing the input and then the assigned path gives the index-sensitive source rule. -/
def indexedSourcePath (G : Arcs V) (S : Finset V) (i : ℕ) (d : V × V) : Option (List (V × V)) :=
  reversePath (indexedSinkPath (reverseArcs G) S i d.swap)

theorem knownSourcePath_valid (G : Arcs V) {S : Finset V} (p : ℕ) {d : V × V} (h : d.1 ∈ S) :
    ValidPathChoice G d (knownSourcePath G S p d) := by
  simpa [knownSourcePath] using
    (knownSinkPath_valid (reverseArcs G) p (d := d.swap) h).reverse

theorem indexedSourcePath_valid (G : Arcs V) {S : Finset V} (i : ℕ) {d : V × V} (h : d.1 ∈ S) :
    ValidPathChoice G d (indexedSourcePath G S i d) := by
  simpa [indexedSourcePath] using
    (indexedSinkPath_valid (reverseArcs G) i (d := d.swap) h).reverse

theorem theorem5_sources_known_p (G : Arcs V) (S : Finset V) (p : ℕ) (D : List (V × V))
    (length_le : D.length ≤ p) (hsources : ∀ d ∈ D, d.1 ∈ S) :
    let H := plannedArcs (fun _ => knownSourcePath G S p) D
    H ⊆ G ∧ Preserves G H D ∧
      H.card ≤ 2 * Fintype.card V + 2 * endpointBudget (Fintype.card V) S.card p := by
  have hc := plannedArcs_correct G (fun _ => knownSourcePath G S p) D (fun i =>
    knownSourcePath_valid G p (hsources _ (List.get_mem _ _)))
  refine ⟨hc.1, hc.2, ?_⟩
  have hr := (theorem5_sinks_known_p (reverseArcs G) S p (D.map Prod.swap)
    (by simpa using length_le) (by
      intro d hd
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      exact hsources e he)).2.2
  change (plannedArcs (fun _ d => reversePath (knownSinkPath (reverseArcs G) S p d.swap)) D).card ≤ _
  rw [plannedArcs_reverse (fun _ => knownSinkPath (reverseArcs G) S p), reverseArcs_card]
  exact hr

theorem theorem5_sources_indexed (G : Arcs V) (S : Finset V) (D : List (V × V))
    (hsources : ∀ d ∈ D, d.1 ∈ S) :
    let H := plannedArcs (indexedSourcePath G S) D
    H ⊆ G ∧ Preserves G H D ∧
      H.card ≤ 2 * Fintype.card V + 48 * endpointBudget (Fintype.card V) S.card D.length := by
  have hc := plannedArcs_correct G (indexedSourcePath G S) D (fun i =>
    indexedSourcePath_valid G i.1 (hsources _ (List.get_mem _ _)))
  refine ⟨hc.1, hc.2, ?_⟩
  have hr := (theorem5_sinks_indexed (reverseArcs G) S (D.map Prod.swap) (by
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact hsources e he)).2.2
  change (plannedArcs (fun i d => reversePath (indexedSinkPath (reverseArcs G) S i d.swap)) D).card ≤ _
  rw [plannedArcs_reverse (indexedSinkPath (reverseArcs G) S), reverseArcs_card]
  simpa only [List.length_map] using hr

end OnlineReachabilityPreservers
