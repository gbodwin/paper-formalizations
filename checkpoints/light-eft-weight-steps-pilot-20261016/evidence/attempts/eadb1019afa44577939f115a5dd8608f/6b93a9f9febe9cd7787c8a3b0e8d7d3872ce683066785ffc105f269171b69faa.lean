import LightEFTSpanners.NativeComponentExtremal

/-! Soundness of the native insertion test for arbitrary original-ID fault sets. -/
namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

namespace Walk
/-- Change the fault set only after checking every usable retained identity. -/
theorem transfer_faults {G : Graph V E} {A F D : Finset E} {u v : G.vertexSet}
    (w : E → ℝ≥0) (p : Walk G A F u v) (h : ∀ e ∈ A, e ∉ F → e ∉ D) :
    ∃ r : Walk G A D u v, r.weight w = p.weight w := by
  induction p with
  | nil u => exact ⟨.nil u,rfl⟩
  | cons e hl he hf p ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨.cons e hl he (h e he hf) r,by simp [weight,hr]⟩

theorem weight_zero_of_edges {G : Graph V E} {A F : Finset E} {u v : G.vertexSet}
    (w : E → ℝ≥0) (p : Walk G A F u v) (h : ∀ e ∈ A, w e = 0) :
    p.weight w = 0 := by
  induction p with
  | nil => rfl
  | cons e hl he hf p ih => simp [weight,h e he,ih]
end Walk

/-- The local test implies coverage under arbitrary faults, by intersecting
with the selected IDs and then transporting the actual surviving walk. -/
theorem NativeCovered.all_faults {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A : Finset E} {e : E} (h : NativeCovered G w t f A e)
    (F : Finset E) (hF : F.card ≤ f) (u v : G.vertexSet) (hl : G.IsLink e u.val v.val) :
    ∃ p : Walk G A F u v, p.weight w ≤ t * w e := by
  classical
  obtain ⟨p,hp⟩ := h (F ∩ A) inter_subset_right ((card_le_card inter_subset_left).trans hF) u v hl
  obtain ⟨r,hr⟩ := p.transfer_faults w (D := F) (by
    intro d hd hdf hbad
    exact hdf (mem_inter.mpr ⟨hbad,hd⟩))
  exact ⟨r,hr.trans_le hp⟩

/-- Coverage needed for replacement concerns only surviving original edges. -/
def NativeSurvivingCovered (G : Graph V E) (w : E → ℝ≥0) (t : ℝ≥0)
    (f : ℕ) (A : Finset E) (e : E) : Prop :=
  ∀ F : Finset E, F.card ≤ f → e ∉ F → ∀ u v : G.vertexSet,
    G.IsLink e u.val v.val → ∃ p : Walk G A F u v, p.weight w ≤ t * w e

theorem NativeCovered.surviving {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A : Finset E} {e : E} (h : NativeCovered G w t f A e) :
    NativeSurvivingCovered G w t f A e := by
  intro F hF _ u v hl
  exact h.all_faults F hF u v hl

theorem NativeSurvivingCovered.of_mem {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A : Finset E} {e : E} (ht : 1 ≤ t) (he : e ∈ A) :
    NativeSurvivingCovered G w t f A e := by
  intro F _ hf u v hl
  refine ⟨.cons e hl he hf (.nil _),?_⟩
  simpa [Walk.weight] using mul_le_mul_of_nonneg_right ht (zero_le : 0 ≤ w e)

theorem NativeSurvivingCovered.mono {G : Graph V E} {w : E → ℝ≥0} {t : ℝ≥0}
    {f : ℕ} {A B : Finset E} {e : E} (h : NativeSurvivingCovered G w t f A e)
    (hAB : A ⊆ B) : NativeSurvivingCovered G w t f B e := by
  intro F hF hf u v hl
  obtain ⟨p,hp⟩ := h F hF hf u v hl
  exact ⟨p.mono hAB,by simpa using hp⟩

/-- Tail coverage persists whether the next ID is skipped or inserted. -/
theorem nativeGreedy_covers_list [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 ≤ t) (f : ℕ) (seed : Finset E) (es : List E) :
    ∀ e ∈ es, NativeSurvivingCovered G w t f (nativeGreedy G w t f seed es) e := by
  induction es with
  | nil => simp
  | cons d ds ih =>
    intro e he
    simp only [nativeGreedy]
    split
    · rename_i h
      rcases List.mem_cons.mp he with rfl | he
      · exact h.elim (NativeSurvivingCovered.of_mem ht) NativeCovered.surviving
      · exact ih e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact NativeSurvivingCovered.of_mem ht (mem_insert_self _ _)
      · exact (ih e he).mono (subset_insert _ _)

/-- No ordering or completeness assumption is needed to span seed plus list. -/
theorem nativeGreedy_sound [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (t : ℝ≥0) (ht : 1 ≤ t) (f : ℕ) (seed : Finset E) (es : List E) :
    IsEFTSpanner G w (seed ∪ es.toFinset) (nativeGreedy G w t f seed es) f t := by
  apply edgewise_replacement G w _ _ f t (nativeGreedy_subset_input G w t f seed es)
  intro F hF u v e hl he hf
  have hc : NativeSurvivingCovered G w t f (nativeGreedy G w t f seed es) e := by
    rcases mem_union.mp he with hs | hs
    · exact NativeSurvivingCovered.of_mem ht (nativeGreedy_seed_subset G w t f seed es hs)
    · exact nativeGreedy_covers_list G w t ht f seed es e (List.mem_toFinset.mp hs)
  exact hc F hF hf u v hl

theorem IsEFTSpanner.fault_mono {G : Graph V E} {w : E → ℝ≥0} {A H : Finset E}
    {f q : ℕ} {t : ℝ≥0} (h : IsEFTSpanner G w A H q t) (hf : f ≤ q) :
    IsEFTSpanner G w A H f t :=
  ⟨h.1,fun F hF u v p => h.2 F (hF.trans hf) u v p⟩

/-- Zero optimum needs no division: a zero-weight connectivity preserver
already has stretch at every nonnegative factor and every smaller fault budget. -/
theorem zero_weight_preserver_isEFT {G : Graph V E} {w : E → ℝ≥0} {A H : Finset E}
    {f q : ℕ} (h : IsConnectivityPreserver G A H q) (hf : f ≤ q)
    (hz : totalWeight w H = 0) (t : ℝ≥0) : IsEFTSpanner G w A H f t := by
  have he : ∀ e ∈ H, w e = 0 := by
    intro e he
    have hle : w e ≤ totalWeight w H := single_le_sum (fun _ _ => zero_le) he
    exact le_antisymm (hz ▸ hle) zero_le
  refine ⟨h.1,?_⟩
  intro F hF u v p
  obtain ⟨r⟩ := h.2 F (hF.trans hf) u v ⟨p⟩
  exact ⟨r,by rw [r.weight_zero_of_edges w he]; exact zero_le⟩

end LightEFTSpanners.NativeWeighted
