import MinorFreeSpanners.FullStarContraction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact edge accounting for a genuine simple quotient under an arbitrary
vertex map. Internal edges disappear; each nonempty crossing-edge fiber
contributes exactly one quotient edge. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I]

/-- Actual host edges whose endpoints have distinct quotient labels. -/
noncomputable def quotientCrossEdges (G : SimpleGraph V) (f : V → I) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ¬ (Sym2.map f e).IsDiag

/-- Actual host edges whose endpoints collapse to one quotient vertex. -/
noncomputable def quotientInternalEdges (G : SimpleGraph V) (f : V → I) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => (Sym2.map f e).IsDiag

/-- The real simple quotient edge set is exactly the image of crossing
host edges; this suppresses both loops and parallel duplicates. -/
theorem map_edgeFinset_eq_cross_image (G : SimpleGraph V) (f : V → I) :
    (G.map f).edgeFinset = (quotientCrossEdges G f).image (Sym2.map f) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf i j =>
    constructor
    · intro he
      obtain ⟨hne,x,y,hxy,hx,hy⟩ := (map_adj' f G i j).mp (by simpa using he)
      refine Finset.mem_image.mpr ⟨s(x,y),?_,?_⟩
      · simpa [quotientCrossEdges,hx,hy] using And.intro hxy hne
      · simp [hx,hy]
    · intro he
      obtain ⟨e,he,hmap⟩ := Finset.mem_image.mp he
      induction e using Sym2.inductionOn with
      | hf x y =>
        have hh : G.Adj x y ∧ f x ≠ f y := by
          simpa [quotientCrossEdges] using he
        have hm : s(f x,f y) ∈ (G.map f).edgeFinset := by
          simpa using (map_adj_apply' hh.1 hh.2)
        simpa only [Sym2.map_mk] using hmap ▸ hm

/-- Every quotient edge has a nonempty fiber of actual crossing edges. -/
theorem quotient_fiber_nonempty (G : SimpleGraph V) (f : V → I)
    {q : Sym2 I} (hq : q ∈ (G.map f).edgeFinset) :
    ((quotientCrossEdges G f).filter fun e => Sym2.map f e = q).Nonempty := by
  rw [map_edgeFinset_eq_cross_image] at hq
  obtain ⟨e,he,hf⟩ := Finset.mem_image.mp hq
  exact ⟨e,Finset.mem_filter.mpr ⟨he,hf⟩⟩

/-- Exact host edge decomposition into internal edges and crossing fibers. -/
theorem quotient_edge_fiber_sum (G : SimpleGraph V) (f : V → I) :
    G.edgeFinset.card = (quotientInternalEdges G f).card +
      ∑ q ∈ (G.map f).edgeFinset,
        ((quotientCrossEdges G f).filter fun e => Sym2.map f e = q).card := by
  classical
  have hp := Finset.card_filter_add_card_filter_not
    (s := G.edgeFinset) (p := fun e => (Sym2.map f e).IsDiag)
  have hs := Finset.card_eq_sum_card_image (Sym2.map f) (quotientCrossEdges G f)
  rw [← map_edgeFinset_eq_cross_image] at hs
  change (quotientInternalEdges G f).card + (quotientCrossEdges G f).card = _ at hp
  omega

/-- Exact loss counts one discarded copy for each excess fiber edge, plus
all internal edges. No cleaning estimate is assumed. -/
theorem quotient_edge_loss (G : SimpleGraph V) (f : V → I) :
    (G.map f).edgeFinset.card + (quotientInternalEdges G f).card +
      ∑ q ∈ (G.map f).edgeFinset,
        (((quotientCrossEdges G f).filter fun e => Sym2.map f e = q).card - 1) =
      G.edgeFinset.card := by
  classical
  have hs : ∑ q ∈ (G.map f).edgeFinset,
      ((quotientCrossEdges G f).filter fun e => Sym2.map f e = q).card =
      (G.map f).edgeFinset.card + ∑ q ∈ (G.map f).edgeFinset,
        (((quotientCrossEdges G f).filter fun e => Sym2.map f e = q).card - 1) := by
    have hp : ∀ q ∈ (G.map f).edgeFinset,
        ((quotientCrossEdges G f).filter fun e => Sym2.map f e = q).card =
        1 + (((quotientCrossEdges G f).filter fun e => Sym2.map f e = q).card - 1) := by
      intro q hq
      have := Finset.card_pos.mpr (quotient_fiber_nonempty G f hq)
      omega
    simp_rw [Finset.sum_congr rfl hp,Finset.sum_add_distrib]
    simp
  have h := quotient_edge_fiber_sum G f
  omega

end MinorFreeSpanners
