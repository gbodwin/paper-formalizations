import OnlineReachabilityPreservers.Basic

/-! Algorithms 1 and 2. The search is bounded and every choice has a fixed tie-break. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*} [LinearOrder V]

/-- The minimum of a finite set, if it is nonempty. -/
def least? (s : Finset V) : Option V :=
  if h : s.Nonempty then some (s.min' h) else none

theorem least?_mem {s : Finset V} {v : V} (h : least? s = some v) : v ∈ s := by
  unfold least? at h
  split at h
  · rename_i hs
    cases h
    exact min'_mem s hs
  · simp at h

theorem least?_eq_none {s : Finset V} : least? s = none ↔ s = ∅ := by
  unfold least?
  split
  · rename_i h
    simp [h.ne_empty]
  · rename_i h
    have hs : s = ∅ := not_nonempty_iff_eq_empty.mp h
    simp [hs]

theorem least?_some {s : Finset V} (hs : s.Nonempty) : ∃ v, least? s = some v :=
  ⟨s.min' hs, by simp [least?, hs]⟩

theorem least?_le {s : Finset V} {v w : V} (h : least? s = some v) (hw : w ∈ s) :
    v ≤ w := by
  unfold least? at h
  split at h
  · cases h
    exact min'_le s w hw
  · simp at h

/-- Take a feasible old successor first, using the same order for new successors. -/
def nextVertex (G H : Arcs V) (R : Finset V) (u : V) : Option V :=
  (least? (R.filter (Edge H u))).or (least? (R.filter (Edge G u)))

theorem nextVertex_spec {G H : Arcs V} (sub : H ⊆ G) {R : Finset V} {u v : V}
    (h : nextVertex G H R u = some v) :
    Edge G u v ∧ v ∈ R ∧ (¬ Edge H u v → ∀ w ∈ R, ¬ Edge H u w) := by
  unfold nextVertex at h
  cases old : least? (R.filter (Edge H u)) with
  | some w =>
    have hv : w = v := by simpa [old] using h
    subst w
    obtain ⟨hr, hh⟩ := mem_filter.mp (least?_mem old)
    exact ⟨sub hh, hr, fun hn => (hn hh).elim⟩
  | none =>
    have hv : least? (R.filter (Edge G u)) = some v := by simpa [old] using h
    obtain ⟨hr, hg⟩ := mem_filter.mp (least?_mem hv)
    refine ⟨hg, hr, fun _ w hw hh => ?_⟩
    have : w ∈ R.filter (Edge H u) := mem_filter.mpr ⟨hw, hh⟩
    rw [least?_eq_none.mp old] at this
    exact notMem_empty _ this

theorem nextVertex_some {G H : Arcs V} {R : Finset V} {u v : V}
    (edge : Edge G u v) (hr : v ∈ R) : ∃ w, nextVertex G H R u = some w := by
  unfold nextVertex
  cases hold : least? (R.filter (Edge H u)) with
  | some w => exact ⟨w, by simp⟩
  | none =>
    cases hnew : least? (R.filter (Edge G u)) with
    | some w => exact ⟨w, by simp⟩
    | none =>
      have : v ∈ R.filter (Edge G u) := mem_filter.mpr ⟨hr, edge⟩
      rw [least?_eq_none.mp hnew] at this
      exact (notMem_empty _ this).elim

/-- The bounded walk search keeps the old preserver fixed for this request. -/
def growFrom (G H : Arcs V) (R : Finset V) (t : V) : ℕ → V → Option (List (V × V))
  | 0, u => if u = t then some [] else none
  | k + 1, u =>
    if u = t then some []
    else do
      let v ← nextVertex G H R u
      let tail ← growFrom G H R t k v
      pure ((u, v) :: tail)

theorem growFrom_spec {G H : Arcs V} (sub : H ⊆ G) {R : Finset V} {t u : V}
    {k : ℕ} {path : List (V × V)} (h : growFrom G H R t k u = some path) :
    Walk G u t path ∧ ∀ e ∈ path, e ∉ H → ∀ w ∈ R, ¬ Edge H e.1 w := by
  induction k generalizing u path with
  | zero =>
    unfold growFrom at h
    split at h
    · rename_i eq
      cases eq
      cases h
      exact ⟨Walk.nil _, by simp⟩
    · simp at h
  | succ k ih =>
    by_cases eq : u = t
    · subst u
      have hp : [] = path := by simpa [growFrom] using h
      subst path
      exact ⟨Walk.nil _, by simp⟩
    · cases hv : nextVertex G H R u with
      | none => simp [growFrom, eq, hv] at h
      | some v =>
        cases ht : growFrom G H R t k v with
        | none => simp [growFrom, eq, hv, ht] at h
        | some rest =>
          have hp : (u, v) :: rest = path := by simpa [growFrom, eq, hv, ht] using h
          subst path
          obtain ⟨edge, _, old⟩ := nextVertex_spec sub hv
          obtain ⟨walk, priority⟩ := ih ht
          refine ⟨Walk.cons edge walk, fun e he => ?_⟩
          rcases List.mem_cons.mp he with rfl | he
          · exact old
          · exact priority e he

theorem growFrom_length {G H : Arcs V} {R : Finset V} {t u : V}
    {k : ℕ} {path : List (V × V)} (h : growFrom G H R t k u = some path) :
    path.length ≤ k := by
  induction k generalizing u path with
  | zero =>
    by_cases eq : u = t
    · simp [growFrom, eq] at h
      subst path
      simp
    · simp [growFrom, eq] at h
  | succ k ih =>
    by_cases eq : u = t
    · simp [growFrom, eq] at h
      subst path
      simp
    · cases hv : nextVertex G H R u with
      | none => simp [growFrom, eq, hv] at h
      | some v =>
        cases ht : growFrom G H R t k v with
        | none => simp [growFrom, eq, hv, ht] at h
        | some rest =>
          have hp : (u, v) :: rest = path := by simpa [growFrom, eq, hv, ht] using h
          subst path
          exact Nat.succ_le_succ (ih ht)

variable [Fintype V]

/-- The computation of Algorithm 1. A failed search is represented by `none`. -/
def forwardPath (G H : Arcs V) (s t : V) : Option (List (V × V)) :=
  growFrom G H (reaches G t) t (Fintype.card V) s

theorem forwardPath_length {G H : Arcs V} {s t : V} {path : List (V × V)}
    (h : forwardPath G H s t = some path) : path.length ≤ Fintype.card V :=
  growFrom_length h

theorem forwardPath_spec {G H : Arcs V} (sub : H ⊆ G) {s t : V}
    {path : List (V × V)} (h : forwardPath G H s t = some path) :
    Walk G s t path ∧ ∀ e ∈ path, e ∉ H → ∀ w, Reach G w t → ¬ Edge H e.1 w := by
  obtain ⟨walk, priority⟩ := growFrom_spec sub h
  exact ⟨walk, fun e he hn w hw => priority e he hn w (mem_reaches.mpr hw)⟩

private theorem growFrom_succeeds {G H : Arcs V} (sub : H ⊆ G) (dag : IsDAG G)
    {k : ℕ} {u t : V} (reach : Reach G u t)
    (fuel : Fintype.card V ≤ k + (reaches G u).card) :
    ∃ path, growFrom G H (reaches G t) t k u = some path := by
  induction k generalizing u with
  | zero =>
    by_cases eq : u = t
    · exact ⟨[], by simp [growFrom, eq]⟩
    · rcases reach.cases_head with h | ⟨v, edge, _⟩
      · exact (eq h).elim
      · have := reaches_card_lt dag edge
        have := card_le_univ (s := reaches G v)
        omega
  | succ k ih =>
    by_cases eq : u = t
    · exact ⟨[], by simp [growFrom, eq]⟩
    · rcases reach.cases_head with h | ⟨v, edge, hvt⟩
      · exact (eq h).elim
      · obtain ⟨w, hw⟩ := nextVertex_some (H := H) edge (mem_reaches.mpr hvt)
        obtain ⟨huw, hwt, _⟩ := nextVertex_spec sub hw
        have hlt := reaches_card_lt dag huw
        obtain ⟨rest, hrest⟩ := ih (mem_reaches.mp hwt) (by omega)
        exact ⟨(u, w) :: rest, by simp [growFrom, eq, hw, hrest]⟩

theorem forwardPath_succeeds {G H : Arcs V} (sub : H ⊆ G) (dag : IsDAG G) {s t : V} :
    (∃ path, forwardPath G H s t = some path) ↔ Reach G s t := by
  refine ⟨fun ⟨_, h⟩ => (forwardPath_spec sub h).1.reachable, fun h => ?_⟩
  exact growFrom_succeeds sub dag h (by omega)

/-- Edges of the selected path. Unreachable requests contribute no edges. -/
def forwardEdges (G H : Arcs V) (d : V × V) : Arcs V :=
  ((forwardPath G H d.1 d.2).getD []).toFinset

def forwardStep (G H : Arcs V) (d : V × V) : Arcs V := H ∪ forwardEdges G H d

theorem forwardEdges_subset {G H : Arcs V} (sub : H ⊆ G) (d : V × V) :
    forwardEdges G H d ⊆ G := by
  intro e he
  unfold forwardEdges at he
  cases hp : forwardPath G H d.1 d.2 with
  | none => simp [hp] at he
  | some path => exact (forwardPath_spec sub hp).1.mem (by simpa [hp] using he)

theorem forwardStep_subset {G H : Arcs V} (sub : H ⊆ G) (d : V × V) :
    forwardStep G H d ⊆ G := union_subset sub (forwardEdges_subset sub d)

theorem forwardStep_reach {G H : Arcs V} (sub : H ⊆ G) (dag : IsDAG G) (d : V × V) :
    Reach (forwardStep G H d) d.1 d.2 ↔ Reach G d.1 d.2 := by
  refine ⟨reach_mono (forwardStep_subset sub d), fun h => ?_⟩
  obtain ⟨path, hp⟩ := (forwardPath_succeeds sub dag).mpr h
  apply reach_mono (H := path.toFinset) _ ((forwardPath_spec sub hp).1.in_edges.reachable)
  intro e he
  exact mem_union_right _ (by simpa [forwardEdges, hp] using he)

theorem no_old_exit_of_new {G H : Arcs V} (sub : H ⊆ G) {d : V × V} {e : V × V}
    (he : e ∈ forwardEdges G H d) (newEdge : e ∉ H) {w : V} (hw : Reach G w d.2) :
    ¬ Edge H e.1 w := by
  unfold forwardEdges at he
  cases hp : forwardPath G H d.1 d.2 with
  | none => simp [hp] at he
  | some path => exact (forwardPath_spec sub hp).2 e (by simpa [hp] using he) newEdge w hw

theorem forward_edge_to_end {G H : Arcs V} (sub : H ⊆ G) {d : V × V} {e : V × V}
    (he : e ∈ forwardEdges G H d) : Reach G e.2 d.2 := by
  unfold forwardEdges at he
  cases hp : forwardPath G H d.1 d.2 with
  | none => simp [hp] at he
  | some path => exact (forwardPath_spec sub hp).1.to_end (by simpa [hp] using he)

theorem forward_edge_order {G H : Arcs V} (sub : H ⊆ G) {d : V × V} {e f : V × V}
    (he : e ∈ forwardEdges G H d) (hf : f ∈ forwardEdges G H d) (hne : e ≠ f) :
    Reach G e.2 f.1 ∨ Reach G f.2 e.1 := by
  unfold forwardEdges at he hf
  cases hp : forwardPath G H d.1 d.2 with
  | none => simp [hp] at he
  | some path =>
    exact (forwardPath_spec sub hp).1.edge_order (by simpa [hp] using he)
      (by simpa [hp] using hf) hne

/-- Algorithm 2 is Algorithm 1 on reversed arcs and reversed endpoints. -/
def backwardPath (G H : Arcs V) (s t : V) : Option (List (V × V)) :=
  (forwardPath (reverseArcs G) (reverseArcs H) t s).map (fun p => p.reverse.map Prod.swap)

end OnlineReachabilityPreservers
