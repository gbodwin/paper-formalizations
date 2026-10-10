import LightEFTSpanners.SeededSubtreePacking
import Mathlib.Algebra.Order.Floor.Semiring

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting

/-- The higher real fault budget has an exact natural-number interpretation. -/
theorem rounded_fault_budget (f : ℕ) {eta : ℝ} (heta : 0≤eta) :
    ⌊(2+eta)*(f:ℝ)⌋₊ = 2*f+⌊eta*(f:ℝ)⌋₊ := by
  rw [show (2+eta)*(f:ℝ)=eta*f+(2*f:ℕ) by push_cast; ring]
  rw [Nat.floor_add_natCast (by positivity)]
  omega

/-- Integer votes retain baseline one and give the uniform repaired finite
coefficient. No upper restriction on eta is used. -/
theorem rounded_charging_le (f : ℕ) {eta L : ℝ} (heta : 0<eta) (hL : 0≤L) :
    1+8*(f:ℝ)*L/(⌊eta*(f:ℝ)⌋₊+1:ℕ) ≤ 1+8*L/eta := by
  have hd : (0:ℝ)<(⌊eta*(f:ℝ)⌋₊+1:ℕ) := by positivity
  have hb := Nat.lt_floor_add_one (eta*(f:ℝ))
  have hp := mul_le_mul_of_nonneg_left hb.le (show 0≤8*L by positivity)
  have hdiv : 8*(f:ℝ)*L/(⌊eta*(f:ℝ)⌋₊+1:ℕ) ≤ 8*L/eta := by
    apply (div_le_div_iff₀ hd heta).mpr
    push_cast
    nlinarith
  linarith

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

/-- The repaired real-eta finite bound for the actual greedy output, conditional
on the explicit subtree packing at the rounded competition budget. -/
theorem seeded_output_rounded_competition {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps eta : ℝ} {f k : ℕ}
    (hQ : IsMinimumFTPreserver G Q w ⌊(2+eta)*(f:ℝ)⌋₊)
    (indices : Finset I) (j : ∀ i, A i ↪ V) (T : ∀ i, SimpleGraph (A i))
    (htrees : ∀ i∈indices, (T i).IsTree)
    (htreeQ : ∀ i∈indices, (T i).map (j i) ≤ Q)
    (hcount : ∀ e∈G.edgeFinset \ Q.edgeFinset,
      ⌊(2+eta)*(f:ℝ)⌋₊+1 ≤ (indices.filter (fun i => ∃ d, (j i).sym2Map d=e)).card)
    (hcong : ∀ e∈Q.edgeFinset,
      (hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card ≤ 2)
    (hw0 : ∀ e, 0≤w e) (hw : ∀ e∈G.edgeSet, 0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+8*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/eta := by
  have hc : ∀ e∈G.edgeFinset \ Q.edgeFinset,
      2*f+(⌊eta*(f:ℝ)⌋₊+1) ≤ (indices.filter (fun i => ∃ d, (j i).sym2Map d=e)).card := by
    intro e he
    simpa only [rounded_fault_budget f heta.le,Nat.add_assoc] using hcount e he
  obtain ⟨hs,hb⟩ := seeded_output_of_subtree_packing hQ indices j T htrees htreeQ
    hc hcong hw0 hw hf hk heps (Nat.succ_pos _)
  refine ⟨hs,hb.trans ?_⟩
  exact rounded_charging_le f heta (by positivity)
end LightEFTSpanners
