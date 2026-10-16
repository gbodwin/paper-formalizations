import LightSpanners.CycleOrder
import LightSpanners.BucketPaths
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace LightSpanners
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- One actual graph walk per starting vertex, whose endpoints are a permutation.
This is the occupancy invariant for an entire hiker squad. -/
structure WalkSquad (G : SimpleGraph V) where
  position : Equiv.Perm V
  path : (v : V) → G.Walk v (position v)

namespace WalkSquad

def refl (G : SimpleGraph V) : WalkSquad G :=
  ⟨Equiv.refl V,fun _ => .nil⟩

def trans (A B : WalkSquad G) : WalkSquad G :=
  ⟨A.position.trans B.position,fun v => (A.path v).append (B.path (A.position v))⟩

noncomputable def swapWalk (d : G.Dart) (v : V) : G.Walk v (Equiv.swap d.fst d.snd v) := by
  classical
  by_cases hv : v = d.fst
  · subst v
    exact (.cons d.adj .nil : G.Walk d.fst d.snd).copy rfl (Equiv.swap_apply_left _ _).symm
  · by_cases hv' : v = d.snd
    · subst v
      exact (.cons d.adj.symm .nil : G.Walk d.snd d.fst).copy rfl (Equiv.swap_apply_right _ _).symm
    · have hs : Equiv.swap d.fst d.snd v = v := Equiv.swap_apply_of_ne_of_ne hv hv'
      exact (.nil : G.Walk v v).copy rfl hs.symm

noncomputable def swap (d : G.Dart) : WalkSquad G :=
  ⟨Equiv.swap d.fst d.snd,swapWalk d⟩

theorem swapWalk_edges (d : G.Dart) (v : V) :
    (swapWalk d v).edges = if v = d.fst then [d.edge] else if v = d.snd then [d.edge] else [] := by
  classical
  by_cases hv : v = d.fst
  · subst v; simp [swapWalk]; rfl
  · by_cases hv' : v = d.snd
    · subst v; simp [swapWalk,hv,Sym2.eq_swap]; rfl
    · simp [swapWalk,hv,hv']

/-- Processing an arbitrary finite chord list by endpoint transpositions. -/
noncomputable def edgeLayer : List G.Dart → WalkSquad G
  | [] => refl G
  | d :: ds => (swap d).trans (edgeLayer ds)

theorem edgeLayer_edges_sublist (ds : List G.Dart) (v : V) :
    List.Sublist ((edgeLayer ds).path v).edges (ds.map Dart.edge) := by
  induction ds generalizing v with
  | nil => simp [edgeLayer,refl]
  | cons d ds ih =>
    change List.Sublist ((swapWalk d v).append ((edgeLayer ds).path (Equiv.swap d.fst d.snd v))).edges _
    rw [Walk.edges_append,swapWalk_edges,List.map_cons]
    split_ifs
    · simpa using (ih (Equiv.swap d.fst d.snd v)).cons_cons d.edge
    · simpa using (ih (Equiv.swap d.fst d.snd v)).cons_cons d.edge
    · simpa using (ih (Equiv.swap d.fst d.snd v)).cons d.edge

variable [Fintype V]
variable {w : Sym2 V → ℝ} (C : UnitSpanningCycle G w)

noncomputable def totalChords (A : WalkSquad G) : ℕ :=
  ∑ v, (C.chordEdges (A.path v)).length

@[simp] theorem totalChords_refl : totalChords C (refl G) = 0 := by
  simp [totalChords,refl]

/-- Occupancy makes total traversal additive under any two squad stages. -/
theorem totalChords_trans (A B : WalkSquad G) :
    totalChords C (A.trans B) = totalChords C A + totalChords C B := by
  change (∑ v, (C.chordEdges ((A.path v).append (B.path (A.position v)))).length) = _
  simp only [C.chordEdges_append,List.length_append,sum_add_distrib,totalChords]
  congr 1
  exact Equiv.sum_comp A.position (fun v => (C.chordEdges (B.path v)).length)

theorem totalChords_swap (d : G.Dart) (hd : d.edge ∉ C.cycle.edges) :
    totalChords C (swap d) = 2 := by
  classical
  have hne : d.fst ≠ d.snd := d.adj.ne
  simp only [totalChords,swap,UnitSpanningCycle.chordEdges,swapWalk_edges]
  have hs (v : V) :
      ((if v = d.fst then [d.edge] else if v = d.snd then [d.edge] else []).filter
        (fun e => e ∉ C.cycle.edges)).length =
      (if v = d.fst then 1 else 0) + (if v = d.snd then 1 else 0) := by
    by_cases hv : v = d.fst
    · subst v; simp [hne,hd]
    · by_cases hv' : v = d.snd
      · subst v; simp [hne.symm,hd]
      · simp [hv,hv']
  simp_rw [hs]
  simp [sum_add_distrib]

/-- Each edge is hiked twice in a layer, even when neighboring chords touch. -/
theorem totalChords_edgeLayer (ds : List G.Dart)
    (hd : ∀ d ∈ ds, d.edge ∉ C.cycle.edges) : totalChords C (edgeLayer ds) = 2*ds.length := by
  induction ds with
  | nil => simp [edgeLayer]
  | cons d ds ih =>
    rw [edgeLayer,totalChords_trans,totalChords_swap C d (hd d (by simp)),
      ih (fun e he => hd e (by simp [he])),List.length_cons]
    omega

/-- An exact averaging lemma for any actual endpoint-permutation squad. -/
theorem exists_long [Nonempty V] (A : WalkSquad G) (k : ℕ)
    (hcount : Fintype.card V*k ≤ totalChords C A) :
    ∃ v, k ≤ (C.chordEdges (A.path v)).length := by
  classical
  by_contra hn
  have hlt : ∀ v : V, (C.chordEdges (A.path v)).length < k := by
    intro v; exact lt_of_not_ge (fun hv => hn ⟨v,hv⟩)
  have hs := sum_lt_sum_of_nonempty univ_nonempty (fun v _ => hlt v)
  simp only [sum_const,card_univ,smul_eq_mul] at hs
  exact (not_lt_of_ge hcount) hs

end WalkSquad
end LightSpanners
