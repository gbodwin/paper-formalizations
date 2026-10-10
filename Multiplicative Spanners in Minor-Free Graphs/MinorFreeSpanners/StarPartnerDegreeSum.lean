import MinorFreeSpanners.NewWitnessBudget
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Distinct actual star partners give disjoint center and leaf vertices.
Their genuine degree sums are bounded by twice the edge count of the
actual induced graph. No density inequality is an assumption. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V I : Type*} [Fintype V] [Fintype I]
attribute [local instance] Classical.propDecidable

/-- Sum degrees over two disjoint injective vertex families in a real graph. -/
theorem degree_sum_two_injections (G : SimpleGraph V) (f g : I → V)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdis : ∀ i j, f i ≠ g j) :
    ∑ i : I, (G.degree (f i)+G.degree (g i)) ≤ 2*G.edgeFinset.card := by
  classical
  let F : I ⊕ I → V := Sum.elim f g
  have hF : Function.Injective F := by
    intro x y he
    cases x with
    | inl x => cases y with
      | inl y => exact congrArg Sum.inl (hf he)
      | inr y => exact (hdis x y he).elim
    | inr x => cases y with
      | inl y => exact (hdis y x he.symm).elim
      | inr y => exact congrArg Sum.inr (hg he)
  calc
    (∑ i : I, (G.degree (f i)+G.degree (g i))) = ∑ x, G.degree (F x) := by
      simp only [Fintype.sum_sum_type,Finset.sum_add_distrib,F,Sum.elim_inl,Sum.elim_inr]
      rfl
    _ = ∑ x ∈ Finset.univ.image F, G.degree x := by
      rw [Finset.sum_image]
      exact hF.injOn
    _ ≤ ∑ x, G.degree x := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

omit [Fintype V] [Fintype I] in
/-- Actual branch ownership and the disjoint left/center domains prove
that every chosen partner leaf is distinct from every partner center. -/
theorem IsStarPacking.partner_vertex_injections {G : SimpleGraph V}
    {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) (hAC : Disjoint A C)
    (f g : I → V) (hf : Function.Injective f)
    (hfC : ∀ i, f i ∈ C) (hgL : ∀ i, g i ∈ L (f i)) :
    Function.Injective g ∧ ∀ i j, f i ≠ g j := by
  constructor
  · intro i j he
    apply hf
    exact h.leaf_owner_unique (hgL i) (by simpa only [he] using hgL j)
  · intro i j he
    exact Finset.disjoint_left.mp hAC (by simpa only [he] using h.2.1 (f j) (hgL j)) (hfC i)

/-- Summing actual partner-degree lower bounds gives a quadratic induced
edge budget. This is a graph counting lemma, ready for the internally
selected minimum-family endpoint from NewWitnessBudget. -/
theorem partner_degree_quadratic (G : SimpleGraph V) (f g : I → V)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdis : ∀ i j, f i ≠ g j) (E : ℝ)
    (hdeg : ∀ i, (Fintype.card I:ℝ) ≤ G.degree (f i)+(G.degree (g i):ℝ)+E) :
    (Fintype.card I:ℝ)*((Fintype.card I:ℝ)-E) ≤ 2*(G.edgeFinset.card:ℝ) := by
  classical
  have hs : ∑ i : I, ((Fintype.card I:ℝ)-E) ≤
      ∑ i : I, ((G.degree (f i):ℝ)+(G.degree (g i):ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    linarith [hdeg i]
  have ht := Nat.cast_le (α:=ℝ).mpr (degree_sum_two_injections G f g hf hg hdis)
  push_cast at ht
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs.trans ht

end MinorFreeSpanners
