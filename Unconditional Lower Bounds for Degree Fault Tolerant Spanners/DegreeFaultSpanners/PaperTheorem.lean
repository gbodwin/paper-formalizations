import DegreeFaultSpanners.ObstructionAssembly
import DegreeFaultSpanners.Parameters
import DegreeFaultSpanners.RealBound
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite

/-!
# End-to-end lower-bound construction

This module constructs an arbitrarily large family for every positive stretch
and fault parameter. Its explicit integer-power inequality is the finite
family form of the paper's lower bound with constant 1/4. The exact-size
interpolation for every `N >= 2` and `1 <= f <= N` is assembled separately.
The k=1 boundary case uses complete graphs; the subset-line construction is
used only for k>=2.

The README and verification record track the complete build, declaration-wide
axiom audit, separate kernel replay, and independent semantic audit.
-/

namespace DegreeFaultSpanners

open SimpleGraph

variable {F : Type*} [Field F] [Fintype F]

/-- The paper's concrete cloud graph, with the corrected dimension domain. -/
def paperGraph (k f : ℕ) : SimpleGraph (Vertex F (k - 2) × Fin f) :=
  cloudGraph (incidenceGraph F (k - 2)) (Fin f)

/-- Both cardinalities are obtained from actual graph bijections. -/
theorem paperGraph_counts (k f : ℕ) (hk : 2 ≤ k) :
    Fintype.card (Vertex F (k - 2) × Fin f) = familyVertices k (Fintype.card F) f ∧
      Nat.card (paperGraph (F := F) k f).edgeSet = familyEdges k (Fintype.card F) f := by
  obtain ⟨hv, he⟩ := lemma6_size F k hk
  constructor
  · rw [Fintype.card_prod, Fintype.card_fin, hv]
    simp only [familyVertices]
    ring
  · rw [paperGraph, cloudGraph_edge_count, Fintype.card_fin, he]
    rfl

/-- Every edge of the actual graph is compulsory, with no geometric premise left. -/
theorem paperGraph_spanner_eq (k f : ℕ) (hk : 2 ≤ k)
    {H : SimpleGraph (Vertex F (k - 2) × Fin f)}
    (hH : IsDegreeFaultSpanner (paperGraph (F := F) k f) H f (2 * k - 1)) :
    H = paperGraph (F := F) k f := by
  apply incidence_cloud_spanner_eq f
  simpa only [paperGraph, Nat.sub_add_cancel hk] using hH

/-- An explicit finite lower-bound witness; the type of vertices is part of the witness. -/
def HasPaperLowerBoundWitness (k f N₀ : ℕ) : Prop :=
  ∃ (V : Type) (inst : Fintype V) (G : SimpleGraph V),
    letI : Fintype V := inst
    N₀ ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧
      ∀ H : SimpleGraph V, IsDegreeFaultSpanner G H f (2 * k - 1) →
        f ^ (k - 1) * Fintype.card V ^ (k + 1) ≤
          4 ^ k * Nat.card H.edgeSet ^ k

/-- The corrected k=1 case, for every fault budget and arbitrarily large size. -/
theorem k_one_lower_bound (f N₀ : ℕ) : HasPaperLowerBoundWitness 1 f N₀ := by
  classical
  let n := max N₀ 2
  refine ⟨Fin n, inferInstance, ⊤, ?_, ?_, ?_⟩
  · rw [Fintype.card_fin]
    exact le_max_left N₀ 2
  · rw [Fintype.card_fin]
    exact le_max_right N₀ 2
  · intro H hH
    have hcard : Nat.card H.edgeSet = n.choose 2 := by
      have h := complete_one_spanner_edge_count (f := f) hH
      simpa only [Nat.card_coe_set_eq, Fintype.card_fin] using h
    rw [Fintype.card_fin, hcard]
    simpa only [Nat.sub_self, pow_zero, one_mul, pow_one] using
      complete_graph_quadratic_lower_bound n (le_max_right _ _)

/-- The incidence construction gives arbitrarily large lower-bound graphs for every k>=2. -/
theorem incidence_family_lower_bound (k f N₀ : ℕ) (hk : 2 ≤ k) (hf : 1 ≤ f) :
    HasPaperLowerBoundWitness k f N₀ := by
  classical
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N₀ 2)
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let V := Vertex (ZMod p) (k - 2) × Fin f
  let G : SimpleGraph V := paperGraph (F := ZMod p) k f
  have hcounts := paperGraph_counts (F := ZMod p) k f hk
  simp only [ZMod.card] at hcounts
  have hlarge : p ≤ familyVertices k p f :=
    familyVertices_ge_parameter k p f (by omega) hp.one_le hf
  refine ⟨V, inferInstance, G, ?_, ?_, ?_⟩
  · change N₀ ≤ Fintype.card (Vertex (ZMod p) (k - 2) × Fin f)
    rw [hcounts.1]
    exact (le_max_left N₀ 2).trans (hpN.trans hlarge)
  · change 2 ≤ Fintype.card (Vertex (ZMod p) (k - 2) × Fin f)
    rw [hcounts.1]
    exact (le_max_right N₀ 2).trans (hpN.trans hlarge)
  · intro H hH
    have hHG : H = G := paperGraph_spanner_eq (F := ZMod p) k f hk hH
    rw [hHG]
    change f ^ (k - 1) * Fintype.card (Vertex (ZMod p) (k - 2) × Fin f) ^ (k + 1) ≤
      4 ^ k * Nat.card (paperGraph (F := ZMod p) k f).edgeSet ^ k
    rw [hcounts.1, hcounts.2]
    exact family_power_lower_bound k p f (by omega)

/-- Theorem 5 in an explicit finite, arbitrarily-large-family form.
Every graph, fault obstruction and cardinality bound is constructed internally. -/
theorem theorem_five (k f N₀ : ℕ) (hk : 1 ≤ k) (hf : 1 ≤ f) :
    HasPaperLowerBoundWitness k f N₀ := by
  by_cases h : k = 1
  · subst k
    exact k_one_lower_bound f N₀
  · exact incidence_family_lower_bound k f N₀ (by omega) hf

/-- The arbitrarily-large-family lower bound with the paper's real exponents,
constant 1/4. This does not yet prescribe the exact number of vertices. -/
theorem theorem_five_real (k f N₀ : ℕ) (hk : 1 ≤ k) (hf : 1 ≤ f) :
    ∃ (V : Type) (inst : Fintype V) (G : SimpleGraph V),
      letI : Fintype V := inst
      N₀ ≤ Fintype.card V ∧ 2 ≤ Fintype.card V ∧
        ∀ H : SimpleGraph V, IsDegreeFaultSpanner G H f (2 * k - 1) →
          (1 / 4 : ℝ) * (f : ℝ) ^ (1 - 1 / (k : ℝ)) *
            (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (Nat.card H.edgeSet : ℝ) := by
  obtain ⟨V, inst, G, hlarge, htwo, hbound⟩ := theorem_five k f N₀ hk hf
  let : Fintype V := inst
  refine ⟨V, inst, G, hlarge, htwo, ?_⟩
  intro H hH
  exact real_lower_bound_of_power k f (Fintype.card V) (Nat.card H.edgeSet) hk (hbound H hH)

end DegreeFaultSpanners
