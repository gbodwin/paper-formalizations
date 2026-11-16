import LightEFTSpanners.CorrectedCloudPaddingTransport
import LightEFTSpanners.FaultBudgetSaturation

/-! An exact unit-ratio fallback at every order n≥2. Padding a single unit
edge suffices because the actual fault-preserver semantics allow components. -/
namespace LightEFTSpanners.CorrectedLowCompetition
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

theorem exists_unit_ratio {n f q : ℕ} {t : ℝ} (hn : 2≤n) :
    ∃ G : SimpleGraph (Fin n), ∃ W : Sym2 (Fin n) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin n), IsEFTSpanner G H W t f →
        ∀Q : SimpleGraph (Fin n), IsMinimumFTPreserver G Q W q →
          competitiveLightness H Q W=1) := by
  let j : Fin 2 ↪ Fin n := Fin.castLEEmb hn
  let r : Fin n → Fin 2 := Function.invFun j
  have hj : Function.LeftInverse r j := Function.leftInverse_invFun j.injective
  let G₀ : SimpleGraph (Fin 2) := ⊤
  let w₀ : Sym2 (Fin 2) → ℝ := fun _ => 1
  refine ⟨G₀.map j,CorrectedCloud.Padding.weight r w₀,
    CorrectedCloud.Padding.positive_map j r hj (by intro e he; norm_num [w₀]),?_⟩
  intro H hsp Q hQ
  have hsp₀ := CorrectedCloud.Padding.eft_restrict j r hj hsp
  have hQ₀ := CorrectedCloud.Padding.minimum_preserver_restrict j r hj hQ
  have hHeq : H.comap j=G₀ := preserver_eq_at_large_budget hsp₀.connectivity (by simp)
  have hQeq : Q.comap j=G₀ := preserver_eq_at_large_budget hQ₀.1 (by simp)
  have hw : 0<totalWeight G₀ w₀ := preserver_weight_pos_of_adj
    (self_connectivity_preserver G₀ 0) (by intro e he; norm_num [w₀])
    (show G₀.Adj (0:Fin 2) 1 from by change (0:Fin 2)≠1; decide)
  rw [CorrectedCloud.Padding.competitiveLightness_restrict j r hj hsp.1 hQ.1.1 w₀,
    hHeq,hQeq,competitiveLightness]
  exact div_self hw.ne'

end LightEFTSpanners.CorrectedLowCompetition
