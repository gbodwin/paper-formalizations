import LightSpanners.Construction
import LightSpanners.Girth
import MinorFreeSpanners.Minor

/-! Claims 14–15 and 18–19. The greedy output is the actual ordered edge
construction already verified in the light-spanner project. Claim 19 is
stated with its corrected t+1 threshold. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every cycle has more than r edges; no convention for infinite girth is needed. -/
def GirthAbove (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ a (p : G.Walk a a), p.IsCycle → r < p.length

theorem weightedGirth_girth {G : SimpleGraph V} {w : Sym2 V → ℝ} {r : ℕ}
    (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hg : WeightedGirthAbove G w r) : GirthAbove G r := by
  intro a p hp
  obtain ⟨e, he, hmax⟩ := exists_max_cycle_edge w p hp
  have hb := (hg a p hp e he).trans_le (walkWeight_le_length_mul p w (w e) hmax)
  have hr : (r : ℝ) < p.length :=
    (mul_lt_mul_iff_of_pos_right (hw e (p.edges_subset_edgeSet he))).mp hb
  exact_mod_cast hr

/-- Claim 14, in a stronger form that needs neither connectedness nor
preprocessing to metric edges. -/
theorem greedy_spanner (G : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ)
    (ht : 1 ≤ t) (hw : ∀ e, 0 ≤ w e) :
    IsSpanner G (greedyOutput G w t) w t := by
  simpa only [greedyInput_graph, greedyOutput] using
    greedy_isSpanner w t ht hw (greedyInput G w) (greedyInput_nondiag G w)

theorem greedy_distance (G : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ)
    (ht : 1 ≤ t) (hw : ∀ e, 0 ≤ w e) (u v : V) :
    weightedDistance (greedyOutput G w t) w u v ≤
      ENNReal.ofReal t * weightedDistance G w u v :=
  (greedy_spanner G w t ht hw).distance_le (by linarith) u v

theorem greedy_minorFree (G : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ)
    (h : ℕ) (hG : CliqueMinorFree G h) :
    CliqueMinorFree (greedyOutput G w t) h := by
  apply hG.mono
  have := edgeGraph_mono (greedyEdges_subset w t (greedyInput G w))
  simpa only [greedyInput_graph, greedyOutput] using this

/-- Exact weighted-girth guarantee, including ties in the processing order. -/
theorem greedy_weighted_girth (G : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ)
    (ht : 0 ≤ t + 1) : WeightedGirthAbove (greedyOutput G w t) w (t + 1) :=
  greedy_weightedGirth w t ht (greedyInput G w) (greedyInput_sorted G w)

/-- Claim 15: actual greedy graph, actual branch-set minor exclusion,
and actual simple-cycle edge count. -/
theorem claim15 (G : SimpleGraph V) (w : Sym2 V → ℝ) (k h : ℕ)
    (hk : 1 ≤ k) (hw : ∀ e, 0 < w e) (hG : CliqueMinorFree G h) :
    CliqueMinorFree (greedyOutput G w (2 * k - 1)) h ∧
    GirthAbove (greedyOutput G w (2 * k - 1)) (2 * k) := by
  refine ⟨greedy_minorFree G w _ h hG, weightedGirth_girth (fun e _ => hw e) ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := greedy_weighted_girth G w (2 * k - 1) (by linarith)
  convert h using 1 <;> push_cast <;> ring

/-- Claim 18: the stretch used in Section 4 is (1+sε)(2k−1). -/
theorem claim18 (G : SimpleGraph V) (w : Sym2 V → ℝ) (k : ℕ)
    (s ε : ℝ) (hk : 1 ≤ k) (hs : 0 ≤ s) (he : 0 ≤ ε)
    (hw : ∀ e, 0 ≤ w e) :
    IsSpanner G (greedyOutput G w ((1+s*ε)*(2*k-1))) w ((1+s*ε)*(2*k-1)) := by
  apply greedy_spanner G w _ _ hw
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [mul_nonneg hs he]

/-- Corrected Claim 19: the source writes (1+sε)2k, exceeding the
guaranteed threshold here by sε. -/
theorem claim19_corrected (G : SimpleGraph V) (w : Sym2 V → ℝ) (k h : ℕ)
    (s ε : ℝ) (hk : 1 ≤ k) (hs : 0 ≤ s) (he : 0 ≤ ε)
    (hG : CliqueMinorFree G h) :
    CliqueMinorFree (greedyOutput G w ((1+s*ε)*(2*k-1))) h ∧
    WeightedGirthAbove (greedyOutput G w ((1+s*ε)*(2*k-1))) w
      ((1+s*ε)*(2*k-1)+1) := by
  refine ⟨greedy_minorFree G w _ h hG, greedy_weighted_girth G w _ ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [mul_nonneg hs he]

/-- The repaired threshold still rules out the short lifted cluster cycles
of Claim 23 when the construction constant satisfies s ≥ 4g. This is the
numerical implication only, not a construction of the clustering hierarchy. -/
theorem cluster_threshold_repair (k : ℕ) (g s ε : ℝ) (hk : 1 ≤ k)
    (hg : 0 ≤ g) (hs : 4*g ≤ s) (he : 0 ≤ ε) :
    (1+2*g*ε)*(2*k) ≤ (1+s*ε)*(2*k-1)+1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hse : 4*g*ε ≤ s*ε := mul_le_mul_of_nonneg_right hs he
  have hge : 0 ≤ g*ε := mul_nonneg hg he
  have hprod := mul_nonneg (sub_nonneg.mpr hse) (show 0 ≤ 2*(k:ℝ)-1 by linarith)
  nlinarith [mul_nonneg hge (show 0 ≤ (k:ℝ)-1 by linarith)]

end MinorFreeSpanners
