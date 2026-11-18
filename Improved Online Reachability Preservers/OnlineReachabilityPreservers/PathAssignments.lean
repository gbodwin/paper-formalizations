import OnlineReachabilityPreservers.SimplePaths
import OnlineReachabilityPreservers.DagReduction
import OnlineReachabilityPreservers.KnownBudget

/-! Preassigned simple paths, their irrevocable unions, and their SCC lift. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V]

/-- A path choice is a simple path when it is present, and is present for reachable demands. -/
def ValidPathChoice (G : Arcs V) (d : V × V) (chosen : Option (List (V × V))) : Prop :=
  (∀ p, chosen = some p → SimpleWalk G d.1 d.2 p) ∧
    (Reach G d.1 d.2 → ∃ p, chosen = some p)

theorem ValidPathChoice.arcs_subset {G : Arcs V} {d : V × V} {p : Option (List (V × V))}
    (h : ValidPathChoice G d p) : pathArcs p ⊆ G := by
  intro e he
  cases p with
  | none => simp [pathArcs] at he
  | some p => exact (h.1 p rfl).1.mem (by simpa [pathArcs] using he)

def plannedArcs (choose : ℕ → V × V → Option (List (V × V))) (D : List (V × V)) : Arcs V :=
  (univ : Finset (Fin D.length)).biUnion fun i => pathArcs (choose i.1 (D.get i))

theorem plannedArcs_prefix (choose : ℕ → V × V → Option (List (V × V)))
    {D T : List (V × V)} (h : D <+: T) : plannedArcs choose D ⊆ plannedArcs choose T := by
  obtain ⟨E, rfl⟩ := h
  intro e he
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
  let j : Fin (D ++ E).length := ⟨i.1, by simpa using i.isLt.trans_le (Nat.le_add_right _ _)⟩
  have eq : (D ++ E).get j = D.get i := List.getElem_append_left i.isLt
  exact mem_biUnion.mpr ⟨j, mem_univ _, by rw [eq]; exact hi⟩

theorem plannedArcs_correct (G : Arcs V) (choose : ℕ → V × V → Option (List (V × V)))
    (D : List (V × V)) (valid : ∀ i : Fin D.length, ValidPathChoice G (D.get i) (choose i.1 (D.get i))) :
    plannedArcs choose D ⊆ G ∧ Preserves G (plannedArcs choose D) D := by
  have sub : plannedArcs choose D ⊆ G := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact (valid i).arcs_subset hi
  refine ⟨sub, fun d hd => ⟨reach_mono sub, ?_⟩⟩
  rcases List.mem_iff_get.mp hd with ⟨i, rfl⟩
  intro hr
  obtain ⟨p, hp⟩ := (valid i).2 hr
  apply reach_mono _ ((valid i).1 p hp).1.in_edges.reachable
  intro e he
  refine mem_biUnion.mpr ⟨i, mem_univ _, ?_⟩
  change e ∈ pathArcs (choose i.1 (D.get i))
  rw [hp]
  exact he

theorem plannedArcs_constant_le (choose : V × V → Option (List (V × V))) (D : List (V × V)) :
    plannedArcs (fun _ => choose) D ⊆ D.toFinset.biUnion (fun d => pathArcs (choose d)) := by
  intro e he
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨D.get i, List.mem_toFinset.mpr (List.get_mem _ _), hi⟩

variable [Fintype V]

/-- Realize a quotient path in the original graph by using its crossing arcs and the fixed SCC
connectors. Only the edges of the resulting simple path are assigned to the request. -/
def liftPath (G : Arcs V) (d : V × V) (p : Option (List (V × V))) : Option (List (V × V)) :=
  routePath (connectors G ∪ liftedArcs G (pathArcs p)) d.1 d.2

theorem liftPath_valid (G : Arcs V) (d : V × V) (p : Option (List (V × V)))
    (h : ValidPathChoice (condensation G) (projectDemand G d) p) :
    ValidPathChoice G d (liftPath G d p) := by
  refine ⟨?_, ?_⟩
  · intro l hl
    exact (routePath_some hl).mono
      (union_subset (connectors_subset G) (liftedArcs_subset G _))
  · intro hd
    obtain ⟨l, hl⟩ := h.2 (project_reach hd)
    have hr : Reach (pathArcs p) (componentLabel G d.1) (componentLabel G d.2) := by
      simpa [pathArcs, hl, projectDemand] using (h.1 l hl).1.in_edges.reachable
    exact routePath_succeeds.mpr (lift_selected_reach h.arcs_subset hr _ _ rfl rfl)

theorem liftPath_arcs_subset (G : Arcs V) (d : V × V) (p : Option (List (V × V))) :
    pathArcs (liftPath G d p) ⊆ connectors G ∪ liftedArcs G (pathArcs p) := by
  intro e he
  cases hl : liftPath G d p with
  | none => simp [pathArcs, hl] at he
  | some l => exact (routePath_some hl).1.mem (by simpa [pathArcs, hl] using he)

theorem plannedArcs_lift_subset (G : Arcs V) (choose : ℕ → V × V → Option (List (V × V)))
    (D : List (V × V)) :
    plannedArcs (fun i d => liftPath G d (choose i (projectDemand G d))) D ⊆
      connectors G ∪ liftedArcs G (plannedArcs choose (D.map (projectDemand G))) := by
  intro e he
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
  let j : Fin (D.map (projectDemand G)).length := ⟨i.1, by simp [i.isLt]⟩
  have eq : (D.map (projectDemand G)).get j = projectDemand G (D.get i) := by
    simp [List.get_eq_getElem, j]
  have hsub : pathArcs (choose i.1 (projectDemand G (D.get i))) ⊆
      plannedArcs choose (D.map (projectDemand G)) := by
    intro a ha
    exact mem_biUnion.mpr ⟨j, mem_univ _, by rw [eq]; exact ha⟩
  exact union_subset_union_right (liftedArcs_mono G hsub) (liftPath_arcs_subset G _ _ hi)

theorem plannedArcs_lift_card (G : Arcs V) (choose : ℕ → V × V → Option (List (V × V)))
    (D : List (V × V)) :
    (plannedArcs (fun i d => liftPath G d (choose i (projectDemand G d))) D).card ≤
      2 * Fintype.card V + (plannedArcs choose (D.map (projectDemand G))).card :=
  (card_le_card (plannedArcs_lift_subset G choose D)).trans
    (card_union_le _ _ |>.trans (Nat.add_le_add (connectors_card G) (liftedArcs_card _ _)))

omit [Fintype V]

def reversePath (p : Option (List (V × V))) : Option (List (V × V)) :=
  p.map fun l => l.reverse.map Prod.swap

theorem pathArcs_reversePath (p : Option (List (V × V))) :
    pathArcs (reversePath p) = reverseArcs (pathArcs p) := by
  cases p with
  | none => simp [reversePath, pathArcs, reverseArcs]
  | some l =>
    ext e
    simp [reversePath, pathArcs, reverseArcs, List.mem_map]

theorem ValidPathChoice.reverse {G : Arcs V} {d : V × V} {p : Option (List (V × V))}
    (h : ValidPathChoice G d p) : ValidPathChoice (reverseArcs G) d.swap (reversePath p) := by
  constructor
  · intro l hl
    obtain ⟨l', hp, eq⟩ := Option.map_eq_some_iff.mp hl
    rw [← eq]
    exact (h.1 l' hp).reverse
  · intro hr
    obtain ⟨l, hl⟩ := h.2 (reach_reverseArcs.mp hr)
    exact ⟨l.reverse.map Prod.swap, by simp [reversePath, hl]⟩

theorem plannedArcs_reverse (choose : ℕ → V × V → Option (List (V × V))) (D : List (V × V)) :
    plannedArcs (fun i d => reversePath (choose i d.swap)) D =
      reverseArcs (plannedArcs choose (D.map Prod.swap)) := by
  ext e
  simp only [plannedArcs, mem_biUnion, mem_univ, true_and, pathArcs_reversePath,
    reverseArcs, mem_image]
  constructor
  · rintro ⟨i, a, ha, rfl⟩
    let j : Fin (D.map Prod.swap).length := ⟨i.1, by simp [i.isLt]⟩
    exact ⟨a, ⟨j, by simpa [List.get_eq_getElem, j] using ha⟩, rfl⟩
  · rintro ⟨a, ⟨j, ha⟩, rfl⟩
    let i : Fin D.length := ⟨j.1, by simpa using j.isLt⟩
    exact ⟨i, a, by simpa [List.get_eq_getElem, i] using ha, rfl⟩

end OnlineReachabilityPreservers
