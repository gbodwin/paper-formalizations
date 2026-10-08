import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! A deterministic finite averaging proof of the one-quarter survival bound.
Edges may be oriented arbitrarily, but must have distinct endpoints. -/
namespace LinearDistancePreservers
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem color_fiber_card {u v : V} (hne : u ≠ v) (a b : Bool) :
    (univ.filter fun c : V → Bool => c u = a ∧ c v = b).card =
      (univ.filter fun c : V → Bool => c u = false ∧ c v = true).card := by
  classical
  let norm := fun c : V → Bool => Function.update (Function.update c u false) v true
  let back := fun c : V → Bool => Function.update (Function.update c u a) v b
  have hnorm (c : V → Bool) : norm c u = false ∧ norm c v = true := by
    simp [norm, hne]
  have hback (c : V → Bool) : back c u = a ∧ back c v = b := by
    simp [back, hne]
  have hleft (c : V → Bool) (hc : c u = a ∧ c v = b) : back (norm c) = c := by
    funext z
    by_cases hu : z = u
    · subst z; simp [back, norm, hne, hc.1]
    by_cases hv : z = v
    · subst z; simp [back, norm, hc.2]
    simp [back, norm, hu, hv]
  have hright (c : V → Bool) (hc : c u = false ∧ c v = true) : norm (back c) = c := by
    funext z
    by_cases hu : z = u
    · subst z; simp [back, norm, hne, hc.1]
    by_cases hv : z = v
    · subst z; simp [back, norm, hc.2]
    simp [back, norm, hu, hv]
  apply Finset.card_bij (fun c _ => norm c)
  · intro c hc
    exact mem_filter.mpr ⟨mem_univ _, hnorm c⟩
  · intro c hc d hd heq
    calc c = back (norm c) := (hleft c (mem_filter.mp hc).2).symm
      _ = back (norm d) := congrArg back heq
      _ = d := hleft d (mem_filter.mp hd).2
  · intro c hc
    exact ⟨back c, mem_filter.mpr ⟨mem_univ _, hback c⟩,
      hright c (mem_filter.mp hc).2⟩

theorem four_color_fiber_card {u v : V} (hne : u ≠ v) :
    4 * (univ.filter fun c : V → Bool => c u = false ∧ c v = true).card =
      Fintype.card (V → Bool) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (V → Bool))) (t := (univ : Finset (Bool × Bool)))
    (f := fun c => (c u, c v)) (fun _ _ => mem_univ _)
  simp only [Prod.mk.injEq, Fintype.sum_prod_type] at h
  simp_rw [color_fiber_card hne] at h
  simpa [mul_comm, ← mul_assoc] using h.symm

noncomputable def surviving (E : Finset (V × V)) (c : V → Bool) : Finset (V × V) :=
  E.filter fun e => c e.1 = false ∧ c e.2 = true

/-- A concrete coloring retaining at least one quarter of any directed edge set. -/
theorem exists_favorable_cut (E : Finset (V × V))
    (hne : ∀ e ∈ E, e.1 ≠ e.2) :
    ∃ c : V → Bool, E.card ≤ 4 * (surviving E c).card := by
  classical
  have havg : 4 * (∑ c : V → Bool, (surviving E c).card) =
      E.card * Fintype.card (V → Bool) := by
    calc
      _ = ∑ e ∈ E, 4 * (univ.filter fun c : V → Bool =>
          c e.1 = false ∧ c e.2 = true).card := by
        simp only [surviving, card_eq_sum_ones, sum_filter]
        rw [sum_comm, mul_sum]
      _ = ∑ _e ∈ E, Fintype.card (V → Bool) :=
        sum_congr rfl (fun e he => four_color_fiber_card (hne e he))
      _ = _ := by simp [mul_comm]
  obtain ⟨c, hc, hmax⟩ := exists_max_image univ
    (fun c : V → Bool => (surviving E c).card) univ_nonempty
  refine ⟨c, ?_⟩
  have hsum := sum_le_sum hmax
  have htotal : ∑ d : V → Bool, (surviving E d).card ≤
      Fintype.card (V → Bool) * (surviving E c).card := by simpa using hsum
  have hpos : 0 < Fintype.card (V → Bool) := Fintype.card_pos
  have hmul : E.card * Fintype.card (V → Bool) ≤
      (4 * (surviving E c).card) * Fintype.card (V → Bool) := by
    rw [← havg]
    nlinarith
  exact Nat.le_of_mul_le_mul_right hmul hpos

end LinearDistancePreservers
