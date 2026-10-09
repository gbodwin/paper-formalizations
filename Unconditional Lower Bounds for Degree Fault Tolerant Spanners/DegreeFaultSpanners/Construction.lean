import DegreeFaultSpanners.ShortReach
import DegreeFaultSpanners.FaultSpanner

/-!
# The actual matching fault graph

This file turns the algebraic incidence relation into an actual undirected
simple subgraph, and proves the matching assertion of Lemma 11, including
the distinguished edge. The cycle-hitting and final obstruction theorem
must be supplied separately; a matching alone does not prove the result.
-/

namespace DegreeFaultSpanners

open SimpleGraph

variable {F : Type*} [Field F] {d : ℕ}

/-- The fault set with its distinguished incidence adjoined. -/
def matchingGraph (a : Point F d) (l : Line F d) : SimpleGraph (Vertex F d) where
  Adj
    | Sum.inl b, Sum.inr m => augmentedShortFailure a l b m
    | Sum.inr m, Sum.inl b => augmentedShortFailure a l b m
    | _, _ => False
  symm := ⟨by intro v w h; cases v <;> cases w <;> exact h⟩
  loopless := ⟨by intro v; cases v <;> exact not_false⟩

@[simp] theorem matchingGraph_inl_inr (a b : Point F d) (l m : Line F d) :
    (matchingGraph a l).Adj (Sum.inl b) (Sum.inr m) ↔
      augmentedShortFailure a l b m := Iff.rfl

/-- The protected reference edge is part of the matching. -/
theorem matchingGraph_target (a : Point F d) (l : Line F d) :
    (matchingGraph a l).Adj (Sum.inl a) (Sum.inr l) := Or.inl ⟨rfl, rfl⟩

/-- Every edge of the matching is an actual edge of the incidence graph. -/
theorem matchingGraph_le {a : Point F d} {l : Line F d} (ha : a ∈ lineSet l) :
    matchingGraph a l ≤ incidenceGraph F d := by
  intro v w h
  cases v with
  | inl b =>
    cases w with
    | inl c => exact False.elim h
    | inr m => exact augmentedShortFailure_incident ha h
  | inr m =>
    cases w with
    | inl b => exact augmentedShortFailure_incident ha h
    | inr n => exact False.elim h

/-- The matching has at most one neighbor at every vertex. -/
theorem matchingGraph_neighbor_subsingleton {a : Point F d} {l : Line F d}
    (ha : a ∈ lineSet l) (v : Vertex F d) :
    ((matchingGraph a l).neighborSet v).Subsingleton := by
  intro x hx y hy
  cases v with
  | inl b =>
    cases x with
    | inl c => exact False.elim hx
    | inr m =>
      cases y with
      | inl c => exact False.elim hy
      | inr n => exact congrArg Sum.inr (augmentedShortFailure_line_unique ha hx hy)
  | inr m =>
    cases x with
    | inr n => exact False.elim hx
    | inl b =>
      cases y with
      | inr n => exact False.elim hy
      | inl c => exact congrArg Sum.inl (augmentedShortFailure_point_unique hx hy)

/-- Lemma 11 for the constructed undirected graph, including its protected edge. -/
theorem matchingGraph_degree_bound [Fintype F] {a : Point F d} {l : Line F d}
    (ha : a ∈ lineSet l) : HasDegreeBound (matchingGraph a l) 1 := by
  intro v
  exact Set.ncard_le_one_iff_subsingleton.mpr (matchingGraph_neighbor_subsingleton ha v)

/-- Remove the protected edge to obtain the fault graph itself. -/
def failureGraph (a : Point F d) (l : Line F d) : SimpleGraph (Vertex F d) :=
  (matchingGraph a l).deleteEdges {s(Sum.inl a, Sum.inr l)}

@[simp] theorem failureGraph_not_target (a : Point F d) (l : Line F d) :
    ¬ (failureGraph a l).Adj (Sum.inl a) (Sum.inr l) := by
  simp [failureGraph]

/-- The actual fault graph is an admissible degree-one fault set. -/
theorem failureGraph_admissible [Fintype F] {a : Point F d} {l : Line F d}
    (ha : a ∈ lineSet l) : AdmissibleFault (incidenceGraph F d) 1 (failureGraph a l) := by
  refine ⟨((matchingGraph a l).deleteEdges_le _).trans (matchingGraph_le ha), ?_⟩
  intro v
  calc
    ((failureGraph a l).neighborSet v).ncard ≤ ((matchingGraph a l).neighborSet v).ncard :=
      Set.ncard_le_ncard (fun _ h => (SimpleGraph.deleteEdges_adj.mp h).1)
    _ ≤ 1 := matchingGraph_degree_bound ha v

end DegreeFaultSpanners
