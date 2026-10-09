import DirectedFlowCutGap.ShortcutReachability
import DirectedFlowCutGap.CountedResidualSearch

/-!
# Boolean-array shortcut materialization

Every shortcut query invokes the existing counted finite reachability search on
a concrete restricted Boolean matrix. Its adjacency tests read only the input
matrix, the retained removal mask and the two fixed endpoint labels. The
materializer retains one complete Boolean matrix. Only surviving endpoints are
interpreted as vertices of the frozen shortcut construction.

This supplies the graph-computation component of weighted preparation. It does
not construct the rational threshold mask, survivor enumeration or prepared
weight/cost arrays yet. Counter instrumentation is ghost; all underlying array
loops, allocations and fixed-arity vertex comparisons are charged in the same
declared word model as CountedResidualSearch.
-/

namespace DirectedFlowCutGap.EncodedShortcutReachability

open scoped BigOperators
open IntegralNetworkFlow
open IntegralNetworkFlow.Tabulated

structure Input (m : ℕ) where
  adjacency : Vector (Vector Bool m) m
  removed : Vector Bool m

namespace Input
variable {m : ℕ}

def graph (D : Input m) : Digraph (Fin m) where
  Adj u v := D.adjacency[u.val][v.val] = true

def removedSet (D : Input m) : Finset (Fin m) :=
  Finset.univ.filter fun v => D.removed[v.val] = true

@[simp] theorem mem_removedSet (D : Input m) (v : Fin m) :
    v∈D.removedSet ↔ D.removed[v.val] = true := by simp [removedSet]

def restrictedBool (D : Input m) (s t u v : Fin m) : Bool :=
  D.adjacency[u.val][v.val] && (decide (u=s) || D.removed[u.val]) &&
    (decide (v=t) || D.removed[v.val])

def restrictedGraph (D : Input m) (s t : Fin m) : Digraph (Fin m) where
  Adj u v := D.restrictedBool s t u v = true

instance (D : Input m) (s t : Fin m) : DecidableRel (D.restrictedGraph s t).Adj :=
  fun u v => inferInstanceAs (Decidable (D.restrictedBool s t u v = true))

theorem restrictedGraph_eq (D : Input m) (s t : Fin m) :
    D.restrictedGraph s t = ShortcutReachability.restricted D.graph D.removedSet s t := by
  ext u v
  simp [restrictedGraph,restrictedBool,ShortcutReachability.restricted,graph,and_assoc]

/-- At most four random-access reads, two fixed-arity equality tests, four
Boolean operations, branches and decision construction, with conservative
space for field projections. No membership search through a finset occurs. -/
def restrictedTest (D : Input m) (s t u v : Fin m) :
    Decidable ((D.restrictedGraph s t).Adj u v) × ℕ :=
  (inferInstanceAs (Decidable (D.restrictedBool s t u v = true)),24)

def found {A : Type*} {G : Digraph A} {s t : A} : ResidualSearch.Result G s t → Bool
  | .found _ => true
  | .stopped _ => false

theorem found_iff {A : Type*} {G : Digraph A} {s t : A}
    (r : ResidualSearch.Result G s t) : found r = true ↔ Nonempty (SimplePath G s t) := by
  cases r with
  | found p => simp [found]; exact ⟨p⟩
  | stopped h => simp [found,h]

/-- Disallow a self shortcut before searching. The search result is inspected
only for its constructor; no path vertex function is evaluated. -/
def shortcut (D : Input m) (E : ResidualSearch.Enumeration (Fin m))
    (F : Fintype (Fin m)) (s t : Fin m) : Bool × ℕ :=
  letI : Fintype (Fin m) := F
  if s=t then (false,3) else
    let r := CountedSearch.search E (D.restrictedTest s t) s t
    (found r.1,r.2+4)

theorem shortcut_true (D : Input m) (E : ResidualSearch.Enumeration (Fin m))
    (F : Fintype (Fin m)) (s t : Fin m) :
    (D.shortcut E F s t).1 = true ↔
      s≠t ∧ Nonempty (SimplePath (ShortcutReachability.restricted D.graph D.removedSet s t) s t) := by
  by_cases h : s=t
  · simp [shortcut,h]
  · simp only [shortcut,ite_eq_right h,found_iff,restrictedGraph_eq]
    simp [h]

theorem shortcut_refines (D : Input m) (E : ResidualSearch.Enumeration (Fin m))
    (F : Fintype (Fin m)) (s t : ShortcutContraction.Survivor D.removedSet) :
    (D.shortcut E F s.val t.val).1 = true ↔
      (ShortcutContraction.graph D.graph D.removedSet).Adj s t := by
  rw [shortcut_true,ShortcutReachability.shortcut_iff_restricted]

theorem shortcut_work (D : Input m) (E : ResidualSearch.Enumeration (Fin m))
    (F : Fintype (Fin m)) (s t : Fin m) : (D.shortcut E F s t).2 ≤ CountedSearch.searchBound m 24+4 := by
  let : Fintype (Fin m) := F
  have hs := CountedSearch.search_bound E (D.restrictedTest s t) 24
    (by intro u v; exact Nat.le_refl _) s t
  have hcard : @Fintype.card (Fin m) F = m := by
    have he := @Fintype.card_congr (Fin m) (Fin m) F (Fin.fintype m) (Equiv.refl _)
    simpa using he
  rw [hcard] at hs
  unfold shortcut
  split <;> dsimp only <;> omega

@[instance_reducible] def retainedDictionary (E : ResidualSearch.Enumeration (Fin m)) : Fintype (Fin m) :=
  ⟨⟨E.vertices,E.nodup⟩,E.complete⟩

structure Matrix (m : ℕ) where
  adjacency : Vector (Vector Bool m) m
  work : ℕ

/-- The finite enumeration is retained once. Each search is evaluated once and
its Boolean result is retained; both map passes over the intermediate table
are charged. The 100m²+20m+20 allowance includes `Array.ofFn` loop tests and
index arithmetic, row/outer array allocations, projections and writes. -/
def materialize (D : Input m) : Matrix m :=
  let E := ResidualSearch.Enumeration.fin m
  let F := retainedDictionary E
  let cells := Vector.ofFn (n := m) fun s =>
    Vector.ofFn (n := m) fun t => D.shortcut E F s t
  { adjacency := cells.map fun row => row.map Prod.fst
    work := (∑ s : Fin m, ∑ t : Fin m, (cells[s.val][t.val]).2)+100*m^2+20*m+20 }

@[simp] theorem materialize_cell (D : Input m) (s t : Fin m) :
    D.materialize.adjacency[s.val][t.val] =
      (D.shortcut (ResidualSearch.Enumeration.fin m)
        (retainedDictionary (ResidualSearch.Enumeration.fin m)) s t).1 := by simp [materialize]

theorem materialize_refines (D : Input m)
    (s t : ShortcutContraction.Survivor D.removedSet) :
    D.materialize.adjacency[s.val.val][t.val.val] = true ↔
      (ShortcutContraction.graph D.graph D.removedSet).Adj s t := by
  rw [materialize_cell]
  exact D.shortcut_refines _ _ s t

theorem materialize_work (D : Input m) :
    D.materialize.work ≤ m^2*(CountedSearch.searchBound m 24+104)+20*m+20 := by
  have hs : (∑ s : Fin m, ∑ t : Fin m,
      (D.shortcut (ResidualSearch.Enumeration.fin m)
        (retainedDictionary (ResidualSearch.Enumeration.fin m)) s t).2) ≤
      m^2*(CountedSearch.searchBound m 24+4) := by
    calc
      _ ≤ ∑ _s : Fin m, ∑ _t : Fin m, (CountedSearch.searchBound m 24+4) := by
        apply Finset.sum_le_sum
        intro s _
        apply Finset.sum_le_sum
        intro t _
        exact D.shortcut_work _ _ s t
      _ = _ := by simp; ring
  simp only [materialize,Vector.getElem_ofFn,Fin.eta]
  calc
    _ ≤ m^2*(CountedSearch.searchBound m 24+4)+100*m^2+20*m+20 :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hs (100*m^2)) (20*m)) 20
    _ = _ := by ring

end Input
end DirectedFlowCutGap.EncodedShortcutReachability
