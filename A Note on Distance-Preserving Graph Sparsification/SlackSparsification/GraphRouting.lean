import SlackSparsification.GraphBasics
import Mathlib.Tactic

/-! Graph-level routing obligations for the +6 and +4 constructions.
These are supporting lemmas, not stand-alone sparsifier existence claims. -/
namespace SlackSparsification
open SimpleGraph
variable {V : Type*}

/-- The corrected three-segment calculation: H-distances start with ≤. -/
theorem route_three_segments (G H : SimpleGraph V) (s x y t : V) (k : ℕ)
    (hpre : H.edist s x = G.edist s x) (hsuf : H.edist y t = G.edist y t)
    (hmid : H.edist x y ≤ G.edist x y + k)
    (hsplit : G.edist s x + G.edist x y + G.edist y t = G.edist s t) :
    H.edist s t ≤ G.edist s t + k := by
  calc
    _ ≤ H.edist s x + H.edist x t := H.edist_triangle
    _ ≤ H.edist s x + (H.edist x y + H.edist y t) := add_le_add le_rfl H.edist_triangle
    _ ≤ G.edist s x + ((G.edist x y + k) + G.edist y t) := by
      rw [hpre, hsuf]
      exact add_le_add le_rfl (add_le_add hmid le_rfl)
    _ = (G.edist s x + G.edist x y + G.edist y t) + k := by ac_rfl
    _ = _ := by rw [hsplit]

/-- An additive-2 connector between roots adjacent in H to the prefix and
suffix yields additive 6 between those attachment vertices. -/
theorem plus_six_between_attachments (G H : SimpleGraph V) (hHG : H ≤ G)
    (x y r q : V) (hxr : H.Adj x r) (hqy : H.Adj q y)
    (hconnector : H.edist r q ≤ G.edist r q + 2) :
    H.edist x y ≤ G.edist x y + 6 := by
  have hxr' : H.edist x r = 1 := edist_eq_one_iff_adj.mpr hxr
  have hqy' : H.edist q y = 1 := edist_eq_one_iff_adj.mpr hqy
  have hGrx : G.edist r x = 1 := edist_eq_one_iff_adj.mpr (hHG hxr).symm
  have hGyq : G.edist y q = 1 := edist_eq_one_iff_adj.mpr (hHG hqy).symm
  have hG : G.edist r q ≤ (1 + G.edist x y) + 1 := by
    calc
      _ ≤ G.edist r x + G.edist x q := G.edist_triangle
      _ ≤ G.edist r x + (G.edist x y + G.edist y q) := add_le_add le_rfl G.edist_triangle
      _ = _ := by rw [hGrx, hGyq]; ac_rfl
  calc
    _ ≤ H.edist x r + H.edist r y := H.edist_triangle
    _ ≤ H.edist x r + (H.edist r q + H.edist q y) := add_le_add le_rfl H.edist_triangle
    _ ≤ 1 + ((G.edist r q + 2) + 1) := by
      rw [hxr', hqy']
      exact add_le_add le_rfl (add_le_add hconnector le_rfl)
    _ ≤ 1 + ((((1 + G.edist x y) + 1) + 2) + 1) := by gcongr
    _ = G.edist x y + (1 + 1 + 1 + 2 + 1) := by ac_rfl
    _ = _ := by norm_num

/-- The chosen shortest candidate path gives the additive-4 middle route.
The four adjacent edges are explicitly edges of H. -/
theorem plus_four_selected_path (G H : SimpleGraph V)
    (x y r q u v : V) (hxr : H.Adj x r) (hru : H.Adj r u)
    (hvq : H.Adj v q) (hqy : H.Adj q y)
    (hpath : H.edist u v = G.edist u v)
    (hminimal : G.edist u v ≤ G.edist x y) :
    H.edist x y ≤ G.edist x y + 4 := by
  have hxu : H.edist x u ≤ 1 + 1 := by
    simpa only [edist_eq_one_iff_adj.mpr hxr, edist_eq_one_iff_adj.mpr hru]
      using (H.edist_triangle (u := x) (v := r) (w := u))
  have hvy : H.edist v y ≤ 1 + 1 := by
    simpa only [edist_eq_one_iff_adj.mpr hvq, edist_eq_one_iff_adj.mpr hqy]
      using (H.edist_triangle (u := v) (v := q) (w := y))
  calc
    _ ≤ H.edist x u + H.edist u y := H.edist_triangle
    _ ≤ H.edist x u + (H.edist u v + H.edist v y) := add_le_add le_rfl H.edist_triangle
    _ ≤ (1 + 1) + (G.edist x y + (1 + 1)) := by
      exact add_le_add hxu (add_le_add (hpath.trans_le hminimal) hvy)
    _ = G.edist x y + (1 + 1 + 1 + 1) := by ac_rfl
    _ = _ := by norm_num

end SlackSparsification
