import LightEFTSpanners.EvenAdmissiblePair
import LightEFTSpanners.EvenCutRequirement
import LightEFTSpanners.NativeCenterDecomposition

namespace LightEFTSpanners.EvenSplitting
open Finset MultigraphCuts
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Required cut capacity left after the actual center-free core edges have
already been counted. This is computed from the graph and pair relation. -/
noncomputable def nativeDeficit (G : Graph (Option V) E) (P : V → V → Prop)
    (k : ℕ) (S : Finset V) : ℤ := requirement P k S-cutSize (centerCore G) (S:Set V)

theorem nativeDeficit_compl (G : Graph (Option V) E) (P : V → V → Prop)
    (k : ℕ) (S : Finset V) : nativeDeficit G P k Sᶜ=nativeDeficit G P k S := by
  simp only [nativeDeficit,requirement_compl,coe_compl,cutSize_compl]

theorem nativeDeficit_skew (G : Graph (Option V) E) (P : V → V → Prop) (k : ℕ) :
    SkewSupermodular (nativeDeficit G P k) := by
  intro S T
  rcases requirement_skew P k S T with h | h
  · left
    have hc := cutSize_submodular (centerCore G) (S:Set V) (T:Set V)
    simp only [nativeDeficit,coe_inter,coe_union]
    omega
  · right
    have hc := cutSize_posimodular (centerCore G) (S:Set V) (T:Set V)
    simp only [nativeDeficit,coe_sdiff]
    omega

/-- Native even-cut admissibility. The partner is derived from the actual
input multigraph's cut lower bounds and parity, with no Mader primitive. -/
theorem native_exists_admissible_partner (G : Graph (Option V) E)
    (P : V → V → Prop) (k : ℕ)
    (hcuts : ∀ S : Finset V,requirement P k S≤cutSize G (liftSet S))
    (heven : ∀ S : Finset V,Even (cutSize G (liftSet S)))
    (hdegree : 2≤Fintype.card (CenterInc G)) (i : CenterInc G) :
    ∃ j : CenterInc G,j≠i ∧ ∀ S : Finset V,
      centerEnd G i∈S → centerEnd G j∈S → requirement P k S+2≤cutSize G (liftSet S) := by
  have hc (S : Finset V) : nativeDeficit G P k S≤mass (centerEnd G) S := by
    have h := hcuts S
    rw [cutSize_center_decomposition] at h
    unfold nativeDeficit
    omega
  have hp (S : Finset V) : Even (mass (centerEnd G) S-nativeDeficit G P k S) := by
    have h := (heven S).sub (requirement_even P k S)
    rw [cutSize_center_decomposition] at h
    convert h using 1
    unfold nativeDeficit
    ring
  obtain ⟨j,hji,hj⟩ := exists_admissible_partner (centerEnd G) (nativeDeficit G P k)
    hc (nativeDeficit_compl G P k) (nativeDeficit_skew G P k) hp hdegree i
  refine ⟨j,hji,?_⟩
  intro S hiS hjS
  have h := hj S hiS hjS
  rw [cutSize_center_decomposition]
  unfold nativeDeficit at h
  omega
end LightEFTSpanners.EvenSplitting
