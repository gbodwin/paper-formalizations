import LightSpanners.CycleSegments
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Abel

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- The ordered, oriented chord word of an actual walk. -/
noncomputable def chordDarts {u v : V} (p : G.Walk u v) : List G.Dart :=
  p.darts.filter (fun d => d.edge ∉ C.cycle.edges)

@[simp] theorem chordDarts_nil (u : V) : C.chordDarts (.nil : G.Walk u u) = [] := rfl

@[simp] theorem chordDarts_append {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    C.chordDarts (p.append q) = C.chordDarts p ++ C.chordDarts q := by
  simp [chordDarts, Walk.darts_append]

theorem chordDarts_map_edges {u v : V} (p : G.Walk u v) :
    (C.chordDarts p).map Dart.edge = C.chordEdges p := by
  simp only [chordDarts, chordEdges, Walk.edges_eq_map_darts, List.filter_map]
  rfl

/-- Displacement in the actual cycle's cyclic group of positions. -/
noncomputable def displacement (d : G.Dart) : C.Position :=
  C.positionEquiv.symm d.snd - C.positionEquiv.symm d.fst

theorem displacement_forward {d : G.Dart} (hd : d ∈ C.cycle.darts) :
    C.displacement d = 1 := by
  have hs := (C.dart_mem_iff_successor d).mp hd
  have he := C.successor_position (C.positionEquiv.symm d.fst)
  rw [Equiv.apply_symm_apply, hs] at he
  have he' := congrArg C.positionEquiv.symm he
  simp only [Equiv.symm_apply_apply] at he'
  unfold displacement
  rw [he']
  abel

theorem displacement_backward {d : G.Dart} (hd : d.symm ∈ C.cycle.darts) :
    C.displacement d = -1 := by
  have he := C.displacement_forward hd
  change C.positionEquiv.symm d.fst - C.positionEquiv.symm d.snd = 1 at he
  unfold displacement
  rw [← he]
  abel

theorem displacement_sum {u v : V} (p : G.Walk u v) :
    (p.darts.map C.displacement).sum = C.positionEquiv.symm v - C.positionEquiv.symm u := by
  induction p with
  | nil => simp
  | @cons u v z h p ih =>
    simp only [Walk.darts_cons, List.map_cons, List.sum_cons, ih, displacement]
    abel

theorem displacement_split {u v : V} (p : G.Walk u v) :
    (p.darts.map C.displacement).sum =
      ((C.chordDarts p).map C.displacement).sum +
      ((C.cycleDarts p).map C.displacement).sum := by
  induction p with
  | nil => simp [chordDarts,cycleDarts]
  | @cons u v z h p ih =>
    by_cases he : s(u,v) ∈ C.cycle.edges
    · simpa [chordDarts,cycleDarts,Walk.darts_cons,he,add_assoc,add_comm,add_left_comm] using
        congrArg (fun x => C.displacement ⟨(u,v),h⟩ + x) ih
    · simpa [chordDarts,cycleDarts,Walk.darts_cons,he,add_assoc] using
        congrArg (fun x => C.displacement ⟨(u,v),h⟩ + x) ih

/-- Equal forward and backward budgets cancel in the cyclic position group. -/
theorem BucketWalk.cycle_displacement_zero {u v : V} {i s : ℕ} {p : G.Walk u v}
    (h : C.BucketWalk i s p) : ((C.cycleDarts p).map C.displacement).sum = 0 := by
  obtain ⟨_,_,f,b,hfb,hf,hb,hforward,hbackward⟩ := h
  have hfm : f.map C.displacement = List.replicate s 1 := by
    rw [← hf]
    exact List.map_eq_replicate_iff.mpr (fun d hd => C.displacement_forward (hforward d hd))
  have hbm : b.map C.displacement = List.replicate s (-1) := by
    rw [← hb]
    exact List.map_eq_replicate_iff.mpr (fun d hd => C.displacement_backward (hbackward d hd))
  rw [hfb,List.map_append,List.sum_append,hfm,hbm]
  simp

theorem BucketWalk.chord_displacement {u v : V} {i s : ℕ} {p : G.Walk u v}
    (h : C.BucketWalk i s p) :
    ((C.chordDarts p).map C.displacement).sum = C.positionEquiv.symm v - C.positionEquiv.symm u := by
  have hs := C.displacement_split p
  rw [h.cycle_displacement_zero C,add_zero,C.displacement_sum] at hs
  exact hs.symm

/-- The terminal vertex and oriented chord word already determine the initial
vertex of balanced bucket walks, without any girth or weight assumption. -/
theorem BucketWalk.same_start_of_chordDarts {u u' v : V} {i j s t : ℕ}
    {p : G.Walk u v} {q : G.Walk u' v}
    (hp : C.BucketWalk i s p) (hq : C.BucketWalk j t q)
    (he : C.chordDarts p = C.chordDarts q) : u = u' := by
  have hh : C.positionEquiv.symm v - C.positionEquiv.symm u =
      C.positionEquiv.symm v - C.positionEquiv.symm u' := by
    rw [← hp.chord_displacement C, ← hq.chord_displacement C, he]
  exact C.positionEquiv.symm.injective (sub_right_injective hh)

end LightSpanners.UnitSpanningCycle
