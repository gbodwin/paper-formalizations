import LightEFTSpanners.ConstructedSeededPacking
import LightEFTSpanners.RoundedCompetition

namespace LightEFTSpanners
open SimpleGraph LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The actual optimum-seeded output satisfies the repaired finite real-eta
bound. The integer competition budget is exact; no forest family is supplied. -/
theorem constructed_output_rounded_bound {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps eta : ℝ} {f k : ℕ}
    (hQ : IsMinimumFTPreserver G Q w ⌊(2+eta)*(f:ℝ)⌋₊)
    (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+8*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/eta := by
  have hbudget : 2*f+(⌊eta*(f:ℝ)⌋₊+1)≤⌊(2+eta)*(f:ℝ)⌋₊+1 := by
    rw [rounded_fault_budget f heta.le]
    omega
  obtain ⟨hs,hb⟩ := seeded_output_from_constructed_packing hQ hbudget hw0 hw
    hf hk heps (Nat.succ_pos _)
  exact ⟨hs,hb.trans (rounded_charging_le f heta (by positivity))⟩

/-- A genuine finite upper-bound existence statement. The optimum denominator,
Eulerian forest family, projected hosts and greedy spanner are all constructed.
The total zero-denominator ratio convention is inherited explicitly from
competitiveLightness; no positivity of the optimum is assumed. -/
theorem exists_eft_spanner_rounded_coarse_bound (G : SimpleGraph V) (w : Sym2 V → ℝ)
    {eps eta : ℝ} {f k : ℕ}
    (hw0 : ∀ e,0≤w e) (hw : ∀ e∈G.edgeSet,0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta) :
    ∃ Q H : SimpleGraph V,IsMinimumFTPreserver G Q w ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      IsEFTSpanner G H w ((1+eps)*(2*k-1)) f ∧
      competitiveLightness H Q w ≤
        1+8*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/eta := by
  obtain ⟨Q,hQ⟩ := exists_minimum_preserver G w ⌊(2+eta)*(f:ℝ)⌋₊
  exact ⟨Q,output G Q w ((1+eps)*(2*k-1)) f,hQ,
    constructed_output_rounded_bound hQ hw0 hw hf hk heps heta⟩
end LightEFTSpanners
