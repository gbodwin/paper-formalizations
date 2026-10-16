import SlackSparsification.DirectedBasics
import Mathlib.Tactic

/-! Reachability is existence of an allowed directed walk. The cited sourcewise
 theorem is an explicit ordinary hypothesis; no background result is axiomatized. -/
namespace SlackSparsification.Directed
open SimpleGraph Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V] {K : SimpleGraph V}
attribute [local instance] Classical.propDecidable

def Reachable (K : SimpleGraph V) (A : V → V → Prop) (s t : V) : Prop :=
  ∃ p : K.Walk s t, Allowed A p

theorem reachable_mono {A B : V → V → Prop} (h : ∀ u v, A u v → B u v)
    {s t : V} : Reachable K A s t → Reachable K B s t := by
  rintro ⟨p, hp⟩
  exact ⟨p, fun d hd => h _ _ (hp d hd)⟩

theorem reachable_trans {A : V → V → Prop} {s r t : V}
    (h : Reachable K A s r) (h' : Reachable K A r t) : Reachable K A s t := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨q,hq⟩ := h'
  exact ⟨p.append q, (allowed_append A p q).mpr ⟨hp,hq⟩⟩

theorem reachable_reverse {A : V → V → Prop} {s t : V} :
    Reachable K (fun u v => A v u) t s ↔ Reachable K A s t := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p.reverse, (allowed_reverse (fun u v => A v u) p).mpr hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨p.reverse, (allowed_reverse A p).mpr hp⟩

/-- Theorem 5.2 as supported by its cited source: sourcewise reachability.
The bound is expressed with a uniform constant C, for arbitrary demand subsets. -/
def SourcewiseBound (K : SimpleGraph V) (A : V → V → Prop) (C : ℝ) : Prop :=
  ∀ (R : Finset V) (P : Finset (V × V)), (∀ st ∈ P, st.1 ∈ R) →
    ∃ F : Finset (V × V), (∀ e ∈ F, A e.1 e.2) ∧
      (F.card : ℝ) ≤ C * (Real.sqrt (Fintype.card V * (P.card : ℝ) * R.card) + Fintype.card V) ∧
      ∀ st ∈ P, Reachable K A st.1 st.2 → Reachable K (edgeRel F) st.1 st.2

/-- Apply the cited theorem to indexed demands; repeated pairs are deduplicated. -/
theorem sourcewise_indexed {D : Type*} [DecidableEq D] {A : V → V → Prop} {C : ℝ}
    (hC : 0 ≤ C) (hsource : SourcewiseBound K A C) (R : Finset V) (P : Finset D)
    (src dst : D → V) (hR : ∀ i ∈ P, src i ∈ R) :
    ∃ F : Finset (V × V), (∀ e ∈ F, A e.1 e.2) ∧
      (F.card : ℝ) ≤ C * (Real.sqrt (Fintype.card V * (P.card : ℝ) * R.card) + Fintype.card V) ∧
      ∀ i ∈ P, Reachable K A (src i) (dst i) → Reachable K (edgeRel F) (src i) (dst i) := by
  let Q := P.image fun i => (src i,dst i)
  obtain ⟨F,hFA,hcost,hsat⟩ := hsource R Q (by
    intro st hst
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hst
    exact hR i hi)
  refine ⟨F,hFA,hcost.trans ?_, fun i hi => hsat _ (mem_image.mpr ⟨i,hi,rfl⟩)⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply add_le_add_right
  apply Real.sqrt_le_sqrt
  have hQ : (Q.card : ℝ) ≤ P.card := by exact_mod_cast (card_image_le : Q.card ≤ P.card)
  gcongr

/-- Small demand sets use their source projection and cost at most 2Cn
when p² ≤ n. -/
theorem exists_reachability_small {D : Type*} [DecidableEq D] {A : V → V → Prop} {C : ℝ}
    (hC : 0 ≤ C) (hsource : SourcewiseBound K A C) (P : Finset D)
    (src dst : D → V) (hp : P.card ^ 2 ≤ Fintype.card V) :
    ∃ F : Finset (V × V), (∀ e ∈ F, A e.1 e.2) ∧ (F.card : ℝ) ≤ 2 * C * Fintype.card V ∧
      ∀ i ∈ P, Reachable K A (src i) (dst i) → Reachable K (edgeRel F) (src i) (dst i) := by
  obtain ⟨F,hFA,hcost,hsat⟩ := sourcewise_indexed hC hsource (P.image src) P src dst
    (fun i hi => mem_image.mpr ⟨i,hi,rfl⟩)
  have hc : ((P.image src).card : ℝ) ≤ P.card := by exact_mod_cast card_image_le
  have hp' : (P.card : ℝ)^2 ≤ Fintype.card V := by exact_mod_cast hp
  have hs : Real.sqrt (Fintype.card V * (P.card : ℝ) * (P.image src).card) ≤ Fintype.card V := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ (Fintype.card V : ℝ) * P.card by positivity)
      have hh' := mul_le_mul_of_nonneg_left hp' (show 0 ≤ (Fintype.card V : ℝ) by positivity)
      nlinarith
  refine ⟨F,hFA,?_,hsat⟩
  have hh := mul_le_mul_of_nonneg_left hs hC
  nlinarith
end SlackSparsification.Directed
