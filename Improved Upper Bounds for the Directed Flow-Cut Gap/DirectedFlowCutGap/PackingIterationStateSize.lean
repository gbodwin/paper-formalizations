import DirectedFlowCutGap.PackingIterationWidth

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic BinaryRational BinaryFractionalRows

def smallWidth (B t : ℕ) : ℕ := B+t*(2*B+8)
def commonWidth (n B t : ℕ) : ℕ :=
  smallWidth B t+PackingGuard.objectiveWidth n (AdaptivePackingState.normalizedWidth n (smallWidth B t))+B

theorem small_mono (B : ℕ) {t u : ℕ} (h : t≤u) : smallWidth B t≤smallWidth B u := by
  unfold smallWidth
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem common_mono (n B : ℕ) {t u : ℕ} (h : t≤u) : commonWidth n B t≤commonWidth n B u := by
  have hw := small_mono B h
  unfold commonWidth PackingGuard.objectiveWidth AdaptivePackingState.normalizedWidth NormalizedRow.scalarWidth
  gcongr

theorem small_le_common (n B t : ℕ) : smallWidth B t≤commonWidth n B t := by
  unfold commonWidth
  omega

structure StateSized {n : ℕ} (B t : ℕ) (s : BinaryFractionalCore.State n) : Prop where
  weights : ∀ x∈s.weights.toList,StoredBounded x (smallWidth B t)
  loads : ∀ x∈s.loads.toList,StoredBounded x (smallWidth B t)
  total : StoredBounded s.total (smallWidth B t)
  cost : StoredBounded s.bestCost (commonWidth n B t)

theorem sized_mono {n B t u : ℕ} {s : BinaryFractionalCore.State n} (h : StateSized B t s) (htu : t≤u) :
    StateSized B u s :=
  ⟨fun x hx => bounded_mono (h.weights x hx) (small_mono B htu),
    fun x hx => bounded_mono (h.loads x hx) (small_mono B htu),
    bounded_mono h.total (small_mono B htu),bounded_mono h.cost (common_mono n B htu)⟩

theorem step_size {n : ℕ} (capacity : Row n) (oracle : BinaryFractionalCore.Oracle n)
    (s : BinaryFractionalCore.State n) (B t : ℕ)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) (hs : StateSized B t s) :
    StateSized B (t+1) (BinaryFractionalCore.step capacity oracle s).1 := by
  cases stop : (BinaryRational.le one (objective capacity s.weights).1).1 with
  | true =>
    simpa only [BinaryFractionalCore.step,stop,↓reduceIte] using sized_mono hs (Nat.le_succ t)
  | false =>
    rw [AdaptivePackingState.active_step_eq capacity oracle s stop]
    let q := (oracle s.weights).1
    have ha : StoredBounded (get capacity q.bottleneck) B := by
      apply caps
      rw [ScalarQuotientRow.row_toList]
      exact List.mem_ofFn.mpr ⟨q.bottleneck,rfl⟩
    have hw := update_width (get capacity q.bottleneck) capacity.toList s.weights.toList q.mask.toList
      B (smallWidth B t) ha caps hs.weights
    rw [PackingUpdateRow.result_eq_update] at hw
    have hl := loads_width (get capacity q.bottleneck) s.loads.toList q.mask.toList B (smallWidth B t) ha hs.loads
    rw [PackingLoadRow.result_eq_addLoads] at hl
    have ht := add_stored_bounded (stored_raw_bound hs.total) (stored_raw_bound ha)
    have wn : smallWidth B t+2*B+8=smallWidth B (t+1) := by unfold smallWidth;ring
    have ln : smallWidth B t+B+3≤smallWidth B (t+1) := by rw [←wn];omega
    have tn : smallWidth B t+B+2≤smallWidth B (t+1) := by rw [←wn];omega
    have nw : B≤AdaptivePackingState.normalizedWidth n (smallWidth B t) := by
      have bw : B≤smallWidth B t := by unfold smallWidth;omega
      unfold AdaptivePackingState.normalizedWidth NormalizedRow.scalarWidth
      nlinarith
    have norm := PackingStart.best_width s.weights q.mask (smallWidth B t) hs.weights
    have capBig : ∀ x∈capacity.toList,StoredBounded x (AdaptivePackingState.normalizedWidth n (smallWidth B t)) :=
      fun x hx => bounded_mono (caps x hx) nw
    have candidate := PackingGuard.objective_width capacity.toList (normalized s.weights q.mask).1.toList
      (AdaptivePackingState.normalizedWidth n (smallWidth B t)) (by simp) capBig norm
    rw [ObjectiveRow.result_eq_objective] at candidate
    simp only [Vector.length_toList] at candidate
    have cw : PackingGuard.objectiveWidth n (AdaptivePackingState.normalizedWidth n (smallWidth B t))≤
        commonWidth n B (t+1) := by
      have prior : PackingGuard.objectiveWidth n (AdaptivePackingState.normalizedWidth n (smallWidth B t))≤
          commonWidth n B t := by unfold commonWidth;omega
      exact prior.trans (common_mono n B (Nat.le_succ t))
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [AdaptivePackingState.updatedState,wn] using hw
    · exact fun x hx => bounded_mono (hl x hx) ln
    · exact bounded_mono ht tn
    · change StoredBounded (AdaptivePackingState.selectedCost capacity s q) _
      unfold AdaptivePackingState.selectedCost
      split
      · exact bounded_mono hs.cost (common_mono n B (Nat.le_succ t))
      · exact bounded_mono candidate cw
end DirectedFlowCutGap.PackingIteration
