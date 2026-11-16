import LightEFTSpanners.CorrectedCloudPaddingTransport
import LightEFTSpanners.RealStretchLowerFamily

/-! The actual cycle/subdivision lower family, padded to a prescribed larger
order. An order loss of at most two changes the explicit constant to 1/32. -/
namespace LightEFTSpanners.CorrectedLowCompetition
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

theorem exists_cycle_padding_lower (m f q n : ℕ) (hf : 0<f) (hq : q≤2*f-1)
    (t : ℝ) (ht : 1≤t) (hm : 2*⌈t⌉₊≤m+2)
    (hcard : Fintype.card (ParallelSubdivision.Vertex (I:=Fin f) (cycleGraph (m+3)))≤n)
    (hhalf : n≤2*Fintype.card (ParallelSubdivision.Vertex (I:=Fin f) (cycleGraph (m+3)))) :
    ∃ G : SimpleGraph (Fin n), ∃ W : Sym2 (Fin n) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin n), IsEFTSpanner G H W t f →
        ∀Q : SimpleGraph (Fin n), IsMinimumFTPreserver G Q W q →
          (n:ℝ)/(32*(f:ℝ)^2*t)≤competitiveLightness H Q W) := by
  let V := ParallelSubdivision.Vertex (I:=Fin f) (cycleGraph (m+3))
  let G₀ : SimpleGraph V := ParallelSubdivision.graph (I:=Fin f) (cycleGraph (m+3)) ⊔
    ParallelSubdivision.coreGraph (cycleGraph (m+3)) (cycleGraph (m+3))
  let w₀ : Sym2 V → ℝ :=
    ParallelSubdivision.coreWeight (cycleGraph (m+3)) ((m+2)/⌈t⌉₊)
  have htpos : 0<t := by linarith
  have hceil : 0<⌈t⌉₊ := Nat.ceil_pos.mpr htpos
  have hceilR : (0:ℝ)<⌈t⌉₊ := by exact_mod_cast hceil
  have hw : ∀e∈G₀.edgeSet,0<w₀ e := by
    intro e _
    exact ParallelSubdivision.coreWeight_positive (cycleGraph (m+3)) (by positivity) e
  obtain ⟨R,hR,hbound⟩ := ParallelSubdivision.cycle_real_lower_family m f q hf hq t ht hm
  obtain ⟨j⟩ : Nonempty (V ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hcard)
  let : Nonempty V := ⟨Sum.inl 0⟩
  let r : Fin n → V := Function.invFun j
  have hj : Function.LeftInverse r j := Function.leftInverse_invFun j.injective
  refine ⟨G₀.map j,CorrectedCloud.Padding.weight r w₀,
    CorrectedCloud.Padding.positive_map j r hj hw,?_⟩
  intro H hsp Q hQ
  have hsp₀ := CorrectedCloud.Padding.eft_restrict j r hj hsp
  have hQ₀ := CorrectedCloud.Padding.minimum_preserver_restrict j r hj hQ
  rw [CorrectedCloud.Padding.competitiveLightness_restrict j r hj hsp.1 hQ.1.1 w₀]
  have hlower := hbound (H.comap j) hsp₀
  have hchoice := competitiveLightness_choice_independent (H:=H.comap j) hR hQ₀
  rw [hchoice] at hlower
  apply le_trans ?_ hlower
  have hfR : (0:ℝ)<f := by exact_mod_cast hf
  have hhalfR : (n:ℝ)≤2*(Fintype.card V:ℝ) := by exact_mod_cast hhalf
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<32*(f:ℝ)^2*t)
    (by positivity : (0:ℝ)<16*(f:ℝ)^2*t)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hhalfR (by positivity : (0:ℝ)≤16*(f:ℝ)^2*t)]

end LightEFTSpanners.CorrectedLowCompetition
