import LightEFTSpanners.LargeCloudCertificate

/-! Exact fault threshold for a spanning-tree blowup of a complete base.
This characterizes the candidate certificate, not the paper's lower lightness bound. -/
namespace LightEFTSpanners.GenericBlowupFailure
open SimpleGraph

/-- For every tree on a complete base of at least three vertices, the blowup
is a q-fault connectivity certificate exactly when the cloud has more than q
vertices. This includes q=0 and every nonempty finite cloud. -/
theorem complete_tree_certificate_iff [Fintype I] [Nonempty I]
    (n q : ℕ) (hn : 3 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    IsFTConnectivityPreserver (lift (I:=I) (⊤ : SimpleGraph (Fin n)))
      (lift (I:=I) T) q ↔ q < Fintype.card I := by
  letI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa using (show 1 < n by omega))
  constructor
  · intro h
    by_contra! hq
    exact complete_tree_blowup_failure n q hn hq T hT h
  · exact large_cloud_isFTPreserver le_top hT.connected q

/-- q+1 copies suffice for every spanning tree of the complete base. -/
theorem successor_cloud_certificate (n q : ℕ) (hn : 3 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    IsFTConnectivityPreserver (lift (I:=Fin (q+1)) (⊤ : SimpleGraph (Fin n)))
      (lift (I:=Fin (q+1)) T) q := by
  exact (complete_tree_certificate_iff n q hn T hT).mpr (by simp)

/-- The positive boundary is sharp: q copies fail whenever q is positive. -/
theorem boundary_cloud_failure (n q : ℕ) (hn : 3 ≤ n) (hq : 0 < q)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    ¬ IsFTConnectivityPreserver (lift (I:=Fin q) (⊤ : SimpleGraph (Fin n)))
      (lift (I:=Fin q) T) q := by
  letI : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  rw [complete_tree_certificate_iff n q hn T hT]
  simp

end LightEFTSpanners.GenericBlowupFailure
