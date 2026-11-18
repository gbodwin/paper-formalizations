import Mathlib.Data.List.TakeDrop
import OnlineReachabilityPreservers.Growth

/-! The state after each prefix and the ordered family of purchases. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Definition 1 for a trace of demands, including unreachable pairs. -/
def Preserves (G H : Arcs V) (D : List (V × V)) : Prop :=
  ∀ d ∈ D, Reach H d.1 d.2 ↔ Reach G d.1 d.2

def forwardRunFrom (G H : Arcs V) (D : List (V × V)) : Arcs V :=
  D.foldl (forwardStep G) H

def forwardRun (G : Arcs V) (D : List (V × V)) : Arcs V := forwardRunFrom G ∅ D

theorem forwardRunFrom_extends (G H : Arcs V) (D : List (V × V)) :
    H ⊆ forwardRunFrom G H D := by
  induction D generalizing H with
  | nil => exact Subset.rfl
  | cons d ds ih => exact subset_union_left.trans (ih (forwardStep G H d))

theorem forwardRunFrom_subset {G H : Arcs V} (sub : H ⊆ G) (D : List (V × V)) :
    forwardRunFrom G H D ⊆ G := by
  induction D generalizing H with
  | nil => exact sub
  | cons d ds ih => exact ih (forwardStep_subset sub d)

theorem forwardRunFrom_preserves {G H : Arcs V} (sub : H ⊆ G) (dag : IsDAG G)
    (D : List (V × V)) : Preserves G (forwardRunFrom G H D) D := by
  induction D generalizing H with
  | nil => simp [Preserves]
  | cons d ds ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · refine ⟨reach_mono (forwardRunFrom_subset sub _), fun h => ?_⟩
      exact reach_mono (forwardRunFrom_extends G (forwardStep G H e) ds)
        ((forwardStep_reach sub dag e).mpr h)
    · exact ih (forwardStep_subset sub d) e he

theorem forwardRun_append (G : Arcs V) (D D' : List (V × V)) :
    forwardRun G (D ++ D') = forwardRunFrom G (forwardRun G D) D' := by
  simp [forwardRun, forwardRunFrom, List.foldl_append]

theorem forwardRun_prefix (G : Arcs V) {D D' : List (V × V)} (h : D <+: D') :
    forwardRun G D ⊆ forwardRun G D' := by
  obtain ⟨tail, rfl⟩ := h
  rw [forwardRun_append]
  exact forwardRunFrom_extends G _ tail

theorem forwardRun_preserves {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    Preserves G (forwardRun G D) D :=
  forwardRunFrom_preserves (empty_subset _) dag D

def before (G : Arcs V) (D : List (V × V)) (i : ℕ) : Arcs V := forwardRun G (D.take i)

theorem before_subset (G : Arcs V) (D : List (V × V)) (i : ℕ) : before G D i ⊆ G :=
  forwardRunFrom_subset (empty_subset _) _

theorem before_mono (G : Arcs V) (D : List (V × V)) : Monotone (before G D) := by
  intro i j hij
  apply forwardRun_prefix
  have h : (D.take j).take i = D.take i := by simp [List.take_take, min_eq_left hij]
  rw [← h]
  exact List.take_prefix _ _

theorem before_succ (G : Arcs V) (D : List (V × V)) (i : Fin D.length) :
    before G D (i.1 + 1) = forwardStep G (before G D i) (D.get i) := by
  have h := List.take_concat_get' D i.1 i.isLt
  rw [before, ← h, forwardRun_append]
  rfl

/-- The arcs bought on this indexed request. Each has a unique round of purchase. -/
def newEdges (G : Arcs V) (D : List (V × V)) (i : Fin D.length) : Arcs V :=
  forwardEdges G (before G D i) (D.get i) \ before G D i

theorem newEdges_available {G : Arcs V} {D : List (V × V)} {i j : Fin D.length}
    (hij : i < j) : newEdges G D i ⊆ before G D j := by
  refine Subset.trans ?_ (before_mono G D (by exact hij))
  rw [before_succ]
  intro e he
  exact mem_union_right _ (mem_sdiff.mp he).1

theorem newEdges_card_step (G : Arcs V) (D : List (V × V)) (i : Fin D.length) :
    (newEdges G D i).card + (before G D i).card = (before G D (i.1 + 1)).card := by
  rw [before_succ, forwardStep, union_comm]
  exact card_sdiff_add_card _ _

theorem sum_newEdges_card (G : Arcs V) (D : List (V × V)) :
    ∑ i : Fin D.length, (newEdges G D i).card = (forwardRun G D).card := by
  have diff : ∀ i : Fin D.length,
      (newEdges G D i).card = (before G D (i.1 + 1)).card - (before G D i).card := by
    intro i
    have := newEdges_card_step G D i
    omega
  let m (i : ℕ) := (before G D i).card
  simp_rw [diff]
  have telescope (k : ℕ) : (∑ i ∈ range k, (m (i + 1) - m i)) = m k := by
    induction k with
    | zero => simp [m, before, forwardRun, forwardRunFrom]
    | succ k ih =>
      rw [sum_range_succ, ih, Nat.add_sub_of_le]
      exact card_le_card (before_mono G D (Nat.le_succ k))
  calc
    _ = ∑ i ∈ range D.length, (m (i + 1) - m i) :=
      Fin.sum_univ_eq_sum_range (fun i => m (i + 1) - m i) D.length
    _ = m D.length := telescope _
    _ = _ := by simp [m, before]

/-- New-edge tails are used for the restricted counting argument. -/
def marks (G : Arcs V) (D : List (V × V)) (i : Fin D.length) : Finset V :=
  (newEdges G D i).image Prod.fst

theorem marks_card {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) (i : Fin D.length) :
    (marks G D i).card = (newEdges G D i).card := by
  apply card_image_of_injOn
  intro e he f hf htail
  by_contra hne
  have sub := before_subset G D i
  have he' := (mem_sdiff.mp he).1
  have hf' := (mem_sdiff.mp hf).1
  have heG := forwardEdges_subset sub _ he'
  have hfG := forwardEdges_subset sub _ hf'
  rcases forward_edge_order sub he' hf' hne with h | h
  · exact dag (show Edge G e.1 e.2 from heG) (htail.symm ▸ h)
  · exact dag (show Edge G f.1 f.2 from hfG) (htail ▸ h)

theorem sum_marks_card {G : Arcs V} (dag : IsDAG G) (D : List (V × V)) :
    ∑ i : Fin D.length, (marks G D i).card = (forwardRun G D).card := by
  simpa only [marks_card dag] using sum_newEdges_card G D

/-- No previously bought edge can leave the tail of a new edge and lead to its target. -/
theorem earlier_edge_conflict {G : Arcs V} {D : List (V × V)} {i j : Fin D.length}
    (hij : i < j) {e f : V × V} (he : e ∈ newEdges G D i) (hf : f ∈ newEdges G D j)
    (htail : e.1 = f.1) (hr : Reach G e.2 (D.get j).2) : False := by
  have h := mem_sdiff.mp hf
  apply no_old_exit_of_new (before_subset G D j) h.1 h.2 hr
  rw [← htail]
  exact newEdges_available hij he

theorem new_edge_reaches_target {G : Arcs V} {D : List (V × V)} {i : Fin D.length}
    {e : V × V} (he : e ∈ newEdges G D i) : Reach G e.2 (D.get i).2 :=
  forward_edge_to_end (before_subset G D i) (mem_sdiff.mp he).1

end OnlineReachabilityPreservers
