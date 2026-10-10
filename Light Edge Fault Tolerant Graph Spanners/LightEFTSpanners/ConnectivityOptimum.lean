import LightEFTSpanners.Basic
import LightSpanners.Weight
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

def IsMinimumFTPreserver (G Q : SimpleGraph V) (w : Sym2 V → ℝ) (f : ℕ) : Prop :=
  IsFTConnectivityPreserver G Q f ∧ ∀ S : SimpleGraph V,
    IsFTConnectivityPreserver G S f → totalWeight Q w ≤ totalWeight S w

omit [Fintype V] in
theorem self_connectivity_preserver (G : SimpleGraph V) (f : ℕ) :
    IsFTConnectivityPreserver G G f := ⟨le_rfl, by intros; rfl⟩

/-- The optimal denominator exists on every finite graph. No connectivity,
positivity or oracle assumption is needed for the finite minimum. -/
theorem exists_minimum_preserver (G : SimpleGraph V) (w : Sym2 V → ℝ) (f : ℕ) :
    ∃ Q : SimpleGraph V, IsMinimumFTPreserver G Q w f := by
  classical
  let S : Set (SimpleGraph V) := {Q | IsFTConnectivityPreserver G Q f}
  have hne : S.Nonempty := ⟨G, self_connectivity_preserver G f⟩
  obtain ⟨Q,hQ,hmin⟩ := Set.exists_min_image S (fun Q => totalWeight Q w)
    (Set.toFinite S) hne
  exact ⟨Q,hQ,hmin⟩

theorem minimum_preserver_weight_unique {G Q R : SimpleGraph V}
    {w : Sym2 V → ℝ} {f : ℕ} (hQ : IsMinimumFTPreserver G Q w f)
    (hR : IsMinimumFTPreserver G R w f) : totalWeight Q w = totalWeight R w :=
  le_antisymm (hQ.2 R hR.1) (hR.2 Q hQ.1)

theorem minimum_preserver_weight_mono {G Q R : SimpleGraph V}
    {w : Sym2 V → ℝ} {f g : ℕ} (hfg : f ≤ g)
    (hQ : IsMinimumFTPreserver G Q w f) (hR : IsMinimumFTPreserver G R w g) :
    totalWeight Q w ≤ totalWeight R w := hQ.2 R (hR.1.fault_mono hfg)

/-- A ratio is kept separate from its choice-independent optimal denominator.
As usual, nontrivial ratio claims will explicitly require positive denominator. -/
noncomputable def competitiveLightness (H Q : SimpleGraph V) (w : Sym2 V → ℝ) : ℝ :=
  totalWeight H w / totalWeight Q w

theorem competitiveLightness_choice_independent {G H Q R : SimpleGraph V}
    {w : Sym2 V → ℝ} {f : ℕ} (hQ : IsMinimumFTPreserver G Q w f)
    (hR : IsMinimumFTPreserver G R w f) :
    competitiveLightness H Q w = competitiveLightness H R w := by
  simp only [competitiveLightness, minimum_preserver_weight_unique hQ hR]

end LightEFTSpanners
