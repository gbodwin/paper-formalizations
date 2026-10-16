import LightEFTSpanners.NativeWeightedReachability

namespace LightEFTSpanners.NativeWeighted
open Finset
variable {V E : Type*}

/-- Restoring the fault of an omitted ID cannot destroy a selected walk. -/
theorem Walk.restore_omitted_fault [DecidableEq E] {G : Graph V E} {H F : Finset E}
    {e : E} (he : e ∉ H) {u v : G.vertexSet} (p : Walk G H (F.erase e) u v) :
    Nonempty (Walk G H F u v) := by
  induction p with
  | nil u => exact ⟨.nil u⟩
  | cons f hl hk hf p ih =>
    obtain ⟨r⟩ := ih
    have hne : f ≠ e := fun h => he (h ▸ hk)
    exact ⟨.cons f hl hk (fun hF => hf (mem_erase.mpr ⟨hne, hF⟩)) r⟩

/-- Every omitted actual edge supplies a surviving demand for every allowed
fault set, even when its own ID is among the faults. -/
theorem omitted_edge_survives [Fintype E] (G : Graph V E) (H : Finset E) (q : ℕ)
    (hH : IsConnectivityPreserver G (inputEdges G) H q) {u v : G.vertexSet} {e : E}
    (he : G.IsLink e u.val v.val) (homit : e ∉ H) (F : Finset E) (hF : F.card ≤ q) :
    Nonempty (Walk G H F u v) := by
  classical
  have hsmall : (F.erase e).card ≤ q := (card_erase_le).trans hF
  have hp : Nonempty (Walk G (inputEdges G) (F.erase e) u v) :=
    ⟨.cons e he (Set.mem_toFinset.mpr he.edge_mem) (by simp) (.nil v)⟩
  obtain ⟨p⟩ := hH.2 (F.erase e) hsmall u v hp
  exact p.restore_omitted_fault homit

/-- The omitted-edge demand has native threshold q+1 in the actual seed. -/
theorem omitted_edge_faultConnected [Fintype E] (G : Graph V E) (H : Finset E) (q : ℕ)
    (hH : IsConnectivityPreserver G (inputEdges G) H q) {u v : G.vertexSet} {e : E}
    (he : G.IsLink e u.val v.val) (homit : e ∉ H) :
    MultigraphCuts.FaultConnected (G.restrict (H : Set E)) (q+1)
      (restrictVertexEquiv G H u) (restrictVertexEquiv G H v) := by
  apply (faultConnected_succ_iff G H q u v).mpr
  exact omitted_edge_survives G H q hH he homit

end LightEFTSpanners.NativeWeighted
