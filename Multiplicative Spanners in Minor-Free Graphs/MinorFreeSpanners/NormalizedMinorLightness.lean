import MinorFreeSpanners.CorrectedUnitTreeLightness
import MinorFreeSpanners.ThreeMinorNormalization

/-! The actual minor-preserving MST normalization transfers the constructed
unit-tree bound to arbitrary strictly positive weighted graphs. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
universe u

 theorem normalized_minor_lightness {V : Type u} [Fintype V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (eps : ℝ) (heps : 0<eps) (heps1 : eps≤1)
    (r h : ℕ) (hr : 1≤r) (hh : 3≤h)
    (hn : 2≤Fintype.card V) (hT : IsMinimumSpanningTree G T w)
    (hfree : CliqueMinorFree G h)
    (hG : WeightedGirthAbove G w ((1+eps)*(2*(r:ℝ)-1)+1))
    (hw : ∀ e∈G.edgeSet,0<w e) :
    lightness G T w≤2*(42*(Nat.log 2 (canonicalScale eps)+1:ℕ)+1)*
      canonicalPhaseCredit (canonicalScale eps) r h := by
  let C : ℝ := (42*(Nat.log 2 (canonicalScale eps)+1:ℕ)+1)*
    canonicalPhaseCredit (canonicalScale eps) r h
  have hc : 0≤C := by dsimp [C,canonicalPhaseCredit]; positivity
  have hg : 0≤(1+eps)*(2*(r:ℝ)-1)+1 := by
    have hrR : (1:ℝ)≤r := by exact_mod_cast hr
    nlinarith
  obtain ⟨X,instX,GX,TX,wX,hfreeX,hTX,hwX,hunitX,hgX,_,hlower⟩ :=
    minor_unit_tree_reduction_of_mst_all_h w _ h hh hn hg hT hw hG hfree
  let := instX
  have hb := corrected_unit_tree_lightness eps heps heps1 r h hr (by omega)
    hTX.1 hTX.2.1 hunitX hfreeX hgX (fun e he => (hwX e he).trans' (by norm_num))
  have hweight : totalWeight TX wX=(TX.edgeFinset.card:ℝ) := by
    unfold totalWeight
    calc
      _ = ∑ _e∈TX.edgeFinset,(1:ℝ) := Finset.sum_congr rfl (fun e he => hunitX e (TX.mem_edgeFinset.mp he))
      _ = _ := by simp
  have hlight : lightness GX TX wX≤C := by
    unfold lightness
    rw [hweight]
    by_cases hz : TX.edgeFinset.card=0
    · simpa [hz] using hc
    · have hp : (0:ℝ)<TX.edgeFinset.card := by exact_mod_cast (show 0<TX.edgeFinset.card by omega)
      exact (div_le_iff₀ hp).mpr hb
  change lightness G T w/2≤lightness GX TX wX at hlower
  dsimp [C] at hlight
  nlinarith only [hlower,hlight]

end MinorFreeSpanners
