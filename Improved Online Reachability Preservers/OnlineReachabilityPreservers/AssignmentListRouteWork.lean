import OnlineReachabilityPreservers.SccLiftListWork

/-! Exact list-backed routing in the hop-decreasing subgraph, with operation counts. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def routeEdgeWithWordWork (G : List (V × V)) (t : V) (depth : ℕ) (e : V × V) :
    ((V × V) × Bool) × ℕ :=
  let source := hopsListWithWordWork G e.1 t depth
  let target := hopsListWithWordWork G e.2 t depth
  ((e,decide (target.1 < source.1)),source.2+target.2+7)

private theorem routeEdgeWithWordWork_spec (G : List (V × V)) (t : V) (e : V × V) :
    let n := Fintype.card V
    let out := routeEdgeWithWordWork G t n e
    out.1 = (e,decide (hops G.toFinset e.2 t < hops G.toFinset e.1 t)) ∧
      out.2 ≤ 2*(hopsListWordBudget n G.length)+7 := by
  obtain ⟨source, sourceWork⟩ := hopsListWithWordWork_spec G e.1 t
  obtain ⟨target, targetWork⟩ := hopsListWithWordWork_spec G e.2 t
  constructor
  · simp only [routeEdgeWithWordWork, source, target]
  · exact (Nat.add_le_add_right (Nat.add_le_add sourceWork targetWork) 7).trans_eq (by rw [two_mul])

private def routeArcsListWithWordWork (G : List (V × V)) (t : V) (depth : ℕ) : List (V × V) × ℕ :=
  let tested := mapListWithChecks (routeEdgeWithWordWork G t depth) G
  let keep := tested.1.filter Prod.snd
  (keep.map Prod.fst, tested.2+19*G.length+8)

private def routeArcsListWordBudget (n m : ℕ) : ℕ := m*(2*(hopsListWordBudget n m)+26)+8

private theorem routeArcsListWithWordWork_spec (G : List (V × V)) (t : V) :
    let n := Fintype.card V
    let out := routeArcsListWithWordWork G t n
    out.1.toFinset = G.toFinset.filter (fun e => hops G.toFinset e.2 t < hops G.toFinset e.1 t) ∧
      out.1.length ≤ G.length ∧ out.2 ≤ routeArcsListWordBudget n G.length := by
  let n := Fintype.card V
  let annotate (e : V × V) := (e,decide (hops G.toFinset e.2 t < hops G.toFinset e.1 t))
  let tested := mapListWithChecks (routeEdgeWithWordWork G t n) G
  obtain ⟨same, work⟩ := mapListWithChecks_spec (routeEdgeWithWordWork G t n) annotate G
    (2*(hopsListWordBudget n G.length)+7)
    (fun e _ => (routeEdgeWithWordWork_spec G t e).1)
    (fun e _ => (routeEdgeWithWordWork_spec G t e).2)
  change tested.1 = G.map annotate at same
  refine ⟨?_,?_,?_⟩
  · change ((tested.1.filter Prod.snd).map Prod.fst).toFinset = _
    rw [same]
    ext e
    simp [annotate, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨a, b, ⟨on, rfl⟩, steps⟩
      exact ⟨on, steps⟩
    · rintro ⟨on, steps⟩
      exact ⟨e.1,e.2,⟨on,rfl⟩,steps⟩
  · change ((tested.1.filter Prod.snd).map Prod.fst).length ≤ G.length
    rw [same, List.length_map]
    simpa only [List.length_map] using List.length_filter_le Prod.snd (G.map annotate)
  · change tested.2+19*G.length+8 ≤ _
    exact (Nat.add_le_add_right (Nat.add_le_add_right work _) _).trans_eq (by unfold routeArcsListWordBudget; ring)

/-- Use the exact hop-decreasing filtered network before growing the route.
The tally includes two hop searches for each tested edge. -/
def routePathListWithWordWork (G : List (V × V)) (s t : V) (depth : ℕ) :
    Option (List (V × V)) × ℕ :=
  let selected := routeArcsListWithWordWork G t depth
  let result := forwardPathListWithWordWork selected.1 [] s t depth
  (result.1, selected.2+result.2+4)

def routePathListWordBudget (n m : ℕ) : ℕ :=
  routeArcsListWordBudget n m+reachInListWordBudget n m+(n+1)*(17+n*(2*m+20))+8

theorem routePathListWordBudget_mono_arcs (n : ℕ) : Monotone (routePathListWordBudget n) := by
  intro a b ordered
  unfold routePathListWordBudget routeArcsListWordBudget hopsListWordBudget reachInListWordBudget
  gcongr

theorem routePathListWithWordWork_spec (G : List (V × V)) (s t : V) :
    let n := Fintype.card V
    let out := routePathListWithWordWork G s t n
    out.1 = routePath G.toFinset s t ∧ out.2 ≤ routePathListWordBudget n G.length := by
  let n := Fintype.card V
  let selected := routeArcsListWithWordWork G t n
  let result := forwardPathListWithWordWork selected.1 [] s t n
  obtain ⟨selectedSet, len, cost⟩ := routeArcsListWithWordWork_spec G t
  obtain ⟨same, work, _⟩ := forwardPathListWithWordWork_spec selected.1 [] s t
  constructor
  · change result.1 = _
    rw [show result.1 = _ from same, show selected.1.toFinset = _ from selectedSet]
    rfl
  · have charged : result.2 ≤ reachInListWordBudget n G.length+(n+1)*(17+n*(2*G.length+20))+4 := by
      apply work.trans
      simp only [List.length_nil, Nat.add_zero]
      unfold reachInListWordBudget
      gcongr
    exact (Nat.add_le_add_right (Nat.add_le_add cost charged) 4).trans_eq (by unfold routePathListWordBudget; ring)

end OnlineReachabilityPreservers
