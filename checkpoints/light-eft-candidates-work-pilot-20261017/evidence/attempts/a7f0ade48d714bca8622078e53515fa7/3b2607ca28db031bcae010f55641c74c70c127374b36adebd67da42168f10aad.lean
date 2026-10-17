import LightEFTSpanners.NativeSeedBudget

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}

/-- Positive actual edge weights and one nonloop input edge force a positive
preserver weight. This is separate from the unconditional zero-valid budget. -/
theorem preserver_weight_pos [Fintype E] (G : Graph V E) (w : E → ℝ≥0)
    (H : Finset E) (q : ℕ) (hH : IsConnectivityPreserver G (inputEdges G) H q)
    (hw : ∀ e ∈ G.edgeSet, 0 < w e) {u v : G.vertexSet} {e : E}
    (he : G.IsLink e u.val v.val) (hne : u ≠ v) : 0 < totalWeight w H := by
  classical
  have hp : Nonempty (Walk G (inputEdges G) ∅ u v) :=
    ⟨.cons e he (Set.mem_toFinset.mpr he.edge_mem) (by simp) (.nil v)⟩
  obtain ⟨p⟩ := hH.2 ∅ (by simp) u v hp
  cases p with
  | nil u => exact (hne rfl).elim
  | cons d hl hd _ p =>
    exact (hw d hl.edge_mem).trans_le (single_le_sum (fun _ _ => by positivity) hd)

theorem minimum_weight_pos_of_nonloop [Fintype E] (G : Graph V E) (w : E → ℝ≥0)
    (q : ℕ) (hw : ∀ e ∈ G.edgeSet, 0 < w e) {u v : G.vertexSet} {e : E}
    (he : G.IsLink e u.val v.val) (hne : u ≠ v) :
    0 < minimumPreserverWeight G w (inputEdges G) q := by
  obtain ⟨H,hH,hmin,_⟩ := minimumPreserverWeight_attained G w (inputEdges G) q
  rw [← hmin]
  exact preserver_weight_pos G w H q hH hw he hne

end LightEFTSpanners.NativeWeighted
