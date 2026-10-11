import Mathlib.Tactic

/-! Finite metric accounting for the three additive routing arguments.
These are explicitly supporting reductions, not graph existence theorems. -/
namespace SlackSparsification

/-- The +2 route through a sampled neighbor of a shortest-path vertex. -/
theorem plus_two_route (Hsr Hrt Gst Gsu Gut : ℝ)
    (hleft : Hsr ≤ Gsu + 1) (hright : Hrt ≤ Gut + 1)
    (hsplit : Gsu + Gut = Gst) : Hsr + Hrt ≤ Gst + 2 := by linarith

/-- The +6 route: two endpoint detours, a +2 connector, and two more
unit edges comparing the connector to the original shortest subpath. -/
theorem plus_six_route (Hst Hsr Hrr Hrt Gsu Guv Gvt Grr Gst : ℝ)
    (hroute : Hst ≤ Hsr + Hrr + Hrt)
    (hleft : Hsr ≤ Gsu + 1) (hright : Hrt ≤ Gvt + 1)
    (hconnector : Hrr ≤ Grr + 2) (hcompare : Grr ≤ Guv + 2)
    (hsplit : Gsu + Guv + Gvt = Gst) : Hst ≤ Gst + 6 := by linarith

/-- Corrected Theorem 12 calculation. The first hypothesis is a triangle
inequality, not the unjustified equality printed in the source. -/
theorem plus_four_route (Hst Hxx Gsx Gxt Guu Gxx Gst : ℝ)
    (hroute : Hst ≤ Gsx + Hxx + Gxt)
    (hdetour : Hxx ≤ Guu + 4) (hminimal : Guu ≤ Gxx)
    (hsplit : Gsx + Gxx + Gxt = Gst) : Hst ≤ Gst + 4 := by linarith

/-- A concrete distance table explains why shortest-path membership in G
does not give equality in the triangle inequality for H. Distances in H:
edge st of length 3, edge sx of length 1, edge xt of length 3. Distances in G
also include xt of length 1. Then x lies on a G-shortest path, while
3 = d_H(s,t) < d_H(s,x) + d_H(x,t) = 4. -/
theorem corrected_triangle_arithmetic :
    (1 : ℕ) + 1 = 2 ∧ (3 : ℕ) < 1 + 3 := by decide

/-- If adding a prefix and suffix already covers the missing edges, route
on the original path directly; no ordering of sampled neighbors is needed. -/
theorem overlap_covers {α : Type*} [DecidableEq α]
    (M A B : Finset α) (h : M ⊆ A ∪ B) : M \ (A ∪ B) = ∅ := by
  exact Finset.sdiff_eq_empty_iff_subset.mpr h

end SlackSparsification
