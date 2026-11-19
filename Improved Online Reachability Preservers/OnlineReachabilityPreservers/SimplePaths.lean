import OnlineReachabilityPreservers.Connectors

/-! Extract one deterministic simple path from a directed graph by following decreasing hop layers. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*}

/-- A walk whose vertices, including the final vertex, have no repetitions. -/
def SimpleWalk (G : Arcs V) (s t : V) (path : List (V × V)) : Prop :=
  Walk G s t path ∧ (path.map Prod.fst ++ [t]).Nodup

theorem SimpleWalk.mono {G H : Arcs V} {s t : V} {path : List (V × V)}
    (h : SimpleWalk H s t path) (sub : H ⊆ G) : SimpleWalk G s t path :=
  ⟨h.1.mono sub, h.2⟩

theorem Walk.simple_of_dag {G : Arcs V} (dag : IsDAG G)
    {s t : V} {path : List (V × V)} (w : Walk G s t path) : SimpleWalk G s t path := by
  refine ⟨w, ?_⟩
  induction w with
  | nil => simp
  | @cons u v t rest e w ih =>
    simp only [List.map_cons, List.cons_append, List.nodup_cons]
    refine ⟨fun hu => dag e ?_, ih⟩
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨a, ha, eq⟩ := List.mem_map.mp hu
      exact eq ▸ w.from_start ha
    · have eq : u = t := List.mem_singleton.mp hu
      exact eq.symm ▸ w.reachable

theorem SimpleWalk.reverse [DecidableEq V] {G : Arcs V} {s t : V} {path : List (V × V)}
    (h : SimpleWalk G s t path) :
    SimpleWalk (reverseArcs G) t s (path.reverse.map Prod.swap) := by
  refine ⟨h.1.reverse, ?_⟩
  have eq : (path.reverse.map Prod.swap).map Prod.fst ++ [s] =
      (path.map Prod.fst ++ [t]).reverse := by
    rw [← h.1.vertex_list, List.reverse_cons, List.map_map, List.map_reverse]
    rfl
  rw [eq]
  exact List.nodup_reverse.mpr h.2

variable [LinearOrder V] [Fintype V]

/-- Keep arcs that go toward an earlier reverse-search layer for the target. -/
private def hopGraph (G : Arcs V) (t : V) : Arcs V :=
  G.filter (fun e => hops G e.2 t < hops G e.1 t)

private theorem hopGraph_dag (G : Arcs V) (t : V) : IsDAG (hopGraph G t) := by
  have aux {u v : V} (h : Reach (hopGraph G t) u v) : hops G v t ≤ hops G u t := by
    induction h with
    | refl => exact le_rfl
    | tail _ e ih => exact ((mem_filter.mp e).2).le.trans ih
  intro u v he hv
  exact (not_lt_of_ge (aux hv)) (mem_filter.mp he).2

private theorem hopGraph_reach (G : Arcs V) (t s : V) :
    Reach (hopGraph G t) s t ↔ Reach G s t := by
  refine ⟨reach_mono (filter_subset _ _), ?_⟩
  have aux (k : ℕ) (u : V) (hu : hops G u t = k) (h : Reach G u t) :
      Reach (hopGraph G t) u t := by
    induction k using Nat.strong_induction_on generalizing u with
    | _ k ih =>
      by_cases eq : u = t
      · subst u
        exact .refl
      · obtain ⟨v, edge, hv, hlt⟩ := exists_decreasing_hop h eq
        have hstep : Edge (hopGraph G t) u v := mem_filter.mpr ⟨edge, hlt⟩
        exact (ih _ (hu ▸ hlt) v rfl hv).head hstep
  exact aux _ s rfl

/-- The deterministic path selector used to realize an assignment on the original graph. -/
def routePath (G : Arcs V) (s t : V) : Option (List (V × V)) :=
  forwardPath (hopGraph G t) ∅ s t

theorem routePath_some {G : Arcs V} {s t : V} {path : List (V × V)}
    (h : routePath G s t = some path) : SimpleWalk G s t path :=
  ((forwardPath_spec (empty_subset _) h).1.simple_of_dag (hopGraph_dag G t)).mono
    (filter_subset _ _)

theorem routePath_succeeds {G : Arcs V} {s t : V} :
    (∃ path, routePath G s t = some path) ↔ Reach G s t :=
  (forwardPath_succeeds (empty_subset _) (hopGraph_dag G t)).trans (hopGraph_reach G t s)

private theorem hopGraph_walk_hops {G : Arcs V} {s u t : V} {path : List (V × V)}
    (walk : Walk (hopGraph G t) s u path) (ending : Reach G u t) :
    hops G s t = hops G u t + path.length := by
  induction walk with
  | nil => simp
  | @cons a b z rest edge walk ih =>
    obtain ⟨original, decrease⟩ := mem_filter.mp edge
    change hops G b t < hops G a t at decrease
    have reach : Reach G b t := (walk.mono (filter_subset _ _)).reachable.trans ending
    have oneStep := hops_le_edge (show Edge G a b from original) reach
    have remaining := ih ending
    simp only [List.length_cons]
    omega

/-- The selected original route has the exact minimum hop count. -/
theorem routePath_length_eq_hops {G : Arcs V} {s t : V} {path : List (V × V)}
    (h : routePath G s t = some path) :
    path.length = hops G s t := by
  have walk := (forwardPath_spec (empty_subset _) h).1
  simpa using (hopGraph_walk_hops walk (show Reach G t t from .refl)).symm

end OnlineReachabilityPreservers
