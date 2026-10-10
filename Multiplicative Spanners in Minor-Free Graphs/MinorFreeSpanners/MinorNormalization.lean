import MinorFreeSpanners.SubdivisionMinor
import LightSpanners.TreeReduction

/-! The actual repeated subdivision and reweighting construction, carrying
clique-minor exclusion throughout. No construction trace is assumed.
This version does not need a non-forest premise because it does not claim
a non-forest output. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable
universe u

def MinorBoundedSubdivisionResult (W : Type u) (inst : Fintype W)
    (graphWeight treeWeight : ℝ) (vertexBound : ℕ) (g : ℝ) (h : ℕ) : Prop :=
  letI := inst
  ∃ (G T : SimpleGraph W) (w : Sym2 W → ℝ),
    CliqueMinorFree G h ∧ T ≤ G ∧ T.IsTree ∧ HasBottleneckPaths G T w ∧
    (∀ e ∈ G.edgeSet, 0 < w e) ∧ WeightedGirthAbove G w g ∧
    totalWeight G w = graphWeight ∧ totalWeight T w = treeWeight ∧
    Fintype.card W ≤ vertexBound ∧ (∀ e ∈ T.edgeSet, w e ≤ 1)

/-- Repeated explicit heavy-edge subdivision terminates and adds at most the
initial integer potential many vertices. The result is an actual finite graph. -/
theorem exists_minor_bounded_tree_subdivision_aux (h : ℕ) (hh : 4 ≤ h) (k : ℕ) :
    ∀ (W : Type u) [Fintype W] (G T : SimpleGraph W) (w : Sym2 W → ℝ)
      (g : ℝ), 0 ≤ g → T.IsTree → T ≤ G → HasBottleneckPaths G T w →
      (∀ e ∈ G.edgeSet, 0 < w e) → WeightedGirthAbove G w g →
      subdivisionExcess T w ≤ k → CliqueMinorFree G h →
      ∃ (X : Type u) (instX : Fintype X),
        MinorBoundedSubdivisionResult X instX (totalWeight G w) (totalWeight T w)
          (Fintype.card W + subdivisionExcess T w) g h := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W inst G T w g hg hT hTG hopt hw hG hk hminor
    classical
    by_cases hupper : ∀ e ∈ T.edgeSet, w e ≤ 1
    · exact ⟨W, inst, G, T, w, hminor, hTG, hT, hopt, hw, hG, rfl, rfl, by omega, hupper⟩
    · push Not at hupper
      obtain ⟨e, he, hheavy⟩ := hupper
      induction e using Sym2.inductionOn with
      | hf u v =>
        have huv : T.Adj u v := (mem_edgeSet T).mp he
        let a := w s(u,v) / (subdivisionPieces (w s(u,v)) : ℝ)
        let G1 := subdivideEdge G u v
        let T1 := subdivideEdge T u v
        let w1 := subdivideWeight w u a (w s(u,v) - a)
        obtain ⟨ha, _, hb, _⟩ := subdivision_split_ceiling hheavy
        have hsum : a + (w s(u,v) - a) = w s(u,v) := by ring
        have hsmall : subdivisionExcess T1 w1 < subdivisionExcess T w :=
          subdivisionExcess_decreases huv w hheavy
        obtain ⟨X, instX, GX, TX, wX, hminorX, hTXG, hTX, hoptX, hwX, hgX,
          hweightG, hweightT, hcard, hupperX⟩ :=
          ih (subdivisionExcess T1 w1) (hsmall.trans_le hk) (Option W)
            G1 T1 w1 g hg (subdivideEdge_isTree huv hT) (subdivideEdge_mono hTG u v)
            (hopt.subdivideEdge huv hsum ha.le hb.le)
            (subdivideWeight_positive_edges w hw ha hb)
            (WeightedGirthAbove.subdivideEdge (hTG huv) w hsum ha.le hb.le hg hG) le_rfl (hminor.subdivideEdge (hTG huv) hh)
        let := instX
        refine ⟨X, instX, GX, TX, wX, hminorX, hTXG, hTX, hoptX, hwX, hgX, ?_, ?_, ?_, hupperX⟩
        · exact hweightG.trans (totalWeight_subdivideEdge (hTG huv) w hsum)
        · exact hweightT.trans (totalWeight_subdivideEdge huv w hsum)
        · simp only [Fintype.card_option] at hcard
          omega

/-- An actual finite graph with a unit-weight MST, quantitative lightness
and vertex bounds, weighted girth, and genuine clique-minor exclusion. -/
def MinorUnitTreeReductionResult (W : Type u) (inst : Fintype W)
    (vertexBound : ℕ) (g lowerLightness : ℝ) (h : ℕ) : Prop :=
  letI := inst
  ∃ (G T : SimpleGraph W) (w : Sym2 W → ℝ),
    CliqueMinorFree G h ∧ IsMinimumSpanningTree G T w ∧
    (∀ e ∈ G.edgeSet, 1 ≤ w e) ∧ (∀ e ∈ T.edgeSet, w e = 1) ∧
    WeightedGirthAbove G w g ∧ Fintype.card W ≤ vertexBound ∧
    lowerLightness ≤ lightness G T w

theorem normalized_minor_unit_tree_reduction {U : Type u} [Fintype U]
    {G T : SimpleGraph U} (w : Sym2 U → ℝ) (g : ℝ) (h : ℕ) (hh : 4 ≤ h)
    (hn : 2 ≤ Fintype.card U) (hg : 0 ≤ g) (hT : T.IsTree) (hTG : T ≤ G)
    (hopt : HasBottleneckPaths G T w) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hminor : CliqueMinorFree G h)
    (hnormal : totalWeight T w = (Fintype.card U : ℝ) - 1) :
    ∃ (X : Type u) (instX : Fintype X),
      MinorUnitTreeReductionResult X instX (2 * Fintype.card U - 1) g (lightness G T w / 2) h := by
  classical
  obtain ⟨X, instX, GX, TX, wX, hminorX, hTXG, hTX, hoptX, hwX, hgX,
    hweightG, hweightT, hcard, hupperX⟩ :=
    exists_minor_bounded_tree_subdivision_aux h hh (subdivisionExcess T w) U G T w g hg hT hTG hopt
      hw hG le_rfl hminor
  let := instX
  have hp := subdivisionExcess_le_weight T w (fun e he => (hw e (edgeSet_mono hTG he)).le)
  rw [hnormal] at hp
  have hcast : ((Fintype.card U - 1 : ℕ) : ℝ) = (Fintype.card U : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card U)]
    norm_num
  rw [← hcast] at hp
  have hpNat : subdivisionExcess T w ≤ Fintype.card U - 1 := by exact_mod_cast hp
  have hcard' : Fintype.card X ≤ 2 * Fintype.card U - 1 := by omega
  have hlight : lightness GX TX wX = lightness G T w := by
    simp only [lightness, hweightG, hweightT]
  have hround := normalized_round_up_lightness hTX wX (Fintype.card U) hn hupperX
    (fun e he => (hwX e he).le) (hweightT.trans hnormal) hcard'
  rw [hlight] at hround
  exact ⟨X, instX, GX, TX, (fun e => max 1 (wX e)), hminorX,
    round_up_isMinimumSpanningTree hTX hTXG wX hupperX,
    (fun _ _ => le_max_left _ _), (fun e he => max_eq_left (hupperX e he)),
    hgX.round_up hg hwX, hcard', hround⟩

theorem minor_unit_tree_reduction {U : Type u} [Fintype U]
    {G T : SimpleGraph U} (w : Sym2 U → ℝ) (g : ℝ) (h : ℕ) (hh : 4 ≤ h)
    (hn : 2 ≤ Fintype.card U) (hg : 0 ≤ g) (hT : T.IsTree) (hTG : T ≤ G)
    (hopt : HasBottleneckPaths G T w) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hminor : CliqueMinorFree G h) :
    ∃ (X : Type u) (instX : Fintype X),
      MinorUnitTreeReductionResult X instX (2 * Fintype.card U - 1) g (lightness G T w / 2) h := by
  classical
  have htpos := tree_totalWeight_pos hT hn w (fun e he => hw e (edgeSet_mono hTG he))
  have hnreal : (1 : ℝ) < Fintype.card U := by
    exact_mod_cast (show 1 < Fintype.card U by omega)
  let c := ((Fintype.card U : ℝ) - 1) / totalWeight T w
  have hc : 0 < c := div_pos (by linarith) htpos
  have hnormal : totalWeight T (fun e => c * w e) = (Fintype.card U : ℝ) - 1 := by
    rw [totalWeight_scale]
    dsimp only [c]
    exact div_mul_cancel₀ _ htpos.ne'
  have h := normalized_minor_unit_tree_reduction (fun e => c * w e) g h hh hn hg hT hTG
    (hopt.scale hc.le) (fun e he => mul_pos hc (hw e he))
    ((weightedGirthAbove_scale_iff hc).mpr hG) hminor hnormal
  simpa only [lightness_scale G T w hc] using h

theorem minor_unit_tree_reduction_of_mst {U : Type u} [Fintype U]
    {G T : SimpleGraph U} (w : Sym2 U → ℝ) (g : ℝ) (h : ℕ) (hh : 4 ≤ h)
    (hn : 2 ≤ Fintype.card U) (hg : 0 ≤ g) (hT : IsMinimumSpanningTree G T w)
    (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hminor : CliqueMinorFree G h) :
    ∃ (X : Type u) (instX : Fintype X),
      MinorUnitTreeReductionResult X instX (2 * Fintype.card U - 1) g (lightness G T w / 2) h := by
  classical
  obtain ⟨K, hKG, hK, hopt⟩ := exists_bottleneck_spanning_tree G w
    (hT.2.1.connected.mono hT.1)
  have hKmin := minimumSpanningTree_of_bottleneck hK hKG hopt
  have h := minor_unit_tree_reduction w g h hh hn hg hK hKG hopt hw hG hminor
  simpa only [lightness_mst_independent hKmin hT] using h

end MinorFreeSpanners
