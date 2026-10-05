import BodwinPapers.VFTSpanners.Main
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Basic.ENNReal.Real

namespace BodwinPapers.VFTSpanners
open SimpleGraph
open scoped ENNReal
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

/-- Fault-deleted weighted distance, with value infinity if no walk exists.
For the nonnegative weights used in the main theorem this is the infimum of
the ordinary sums of edge weights. -/
noncomputable def faultDistance (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (F : Finset V) (u v : V) : ℝ≥0∞ :=
  ⨅ p : {p : G.Walk u v // Avoids F p}, ENNReal.ofReal (walkWeight w p.val)

/-- The walk-based stretch guarantee implies the distance inequality in
Definitions 1 and 2, including disconnected vertex pairs. -/
theorem IsVFTSpanner.distance_le {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {k f : ℕ} (h : IsVFTSpanner G H w k f) (hk : 1 ≤ k)
    (F : Finset V) (hF : F.card ≤ f) (u v : V) :
    faultDistance H w F u v ≤ (k : ℝ≥0∞) * faultDistance G w F u v := by
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by simpa using (by omega : k ≠ 0)
  unfold faultDistance
  rw [ENNReal.mul_iInf_of_ne hk0 (by simp)]
  apply le_iInf
  intro p
  obtain ⟨q,hq,hweight⟩ := h.2 F hF u v p.val p.property
  calc
    _ ≤ ENNReal.ofReal (walkWeight w q) := iInf_le (fun p : {p : H.Walk u v // Avoids F p} =>
      ENNReal.ofReal (walkWeight w p.val)) ⟨q,hq⟩
    _ ≤ ENNReal.ofReal ((k : ℝ)*walkWeight w p.val) := ENNReal.ofReal_le_ofReal hweight
    _ = (k : ℝ≥0∞)*ENNReal.ofReal (walkWeight w p.val) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simp

/-- End-to-end statement in distance form, matching the paper's definition
of a vertex-fault-tolerant weighted spanner. -/
theorem vft_greedy_distance_and_size [Fintype V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (k f : ℕ)
    (hk : 1 ≤ k) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    greedyOutput G w k f ≤ G ∧
      (∀ F : Finset V, F.card ≤ f → ∀ u v,
        faultDistance (greedyOutput G w k f) w F u v ≤
          (k : ℝ≥0∞)*faultDistance G w F u v) ∧
      (greedyOutput G w k f).edgeFinset.card ≤
        36*f^2*extremalEdges (max 2 (Fintype.card V / (2*f))) (k+1) := by
  classical
  obtain ⟨hspan,hsize⟩ := vft_greedy_main G w k f hk hf hw
  exact ⟨hspan.1,fun F hF u v => hspan.distance_le hk F hF u v,hsize⟩

end BodwinPapers.VFTSpanners
