import MinorFreeSpanners.ClusterEdgeWeights
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Exact accounting of original host edges between selected old clusters.
A unique-edge quotient does not discard multiplicity silently: injectivity of
the actual host-edge label map is proved before any counting bound is used. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
namespace ClusterFamily
variable {I V : Type*} [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
attribute [local instance] Classical.propDecidable

noncomputable def markedEdges (C : ClusterFamily (I := I) A w D)
    (B : SimpleGraph V) (S : Finset I) : Finset (Sym2 V) := by
  classical
  exact B.edgeFinset.filter fun e =>
    ∃ i∈S, ∃ j∈S, ∃ x∈C.branch i, ∃ y∈C.branch j, e=s(x,y)

/-- Count all original marked edges by the actual induced quotient edges. -/
theorem marked_edges_card_le (C : ClusterFamily (I := I) A w D)
    (hA : A ≤ G) (hB : B ≤ G) (S : Finset I)
    (hloop : ∀ i x, x∈C.branch i → ∀ y, y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x, x∈C.branch i → ∀ y, y∈C.branch j →
      ∀ u, u∈C.branch i → ∀ v, v∈C.branch j →
      B.Adj x y → B.Adj u v → s(x,y)=s(u,v)) :
    (C.markedEdges B S).card ≤ ((C.graph B).induce (S:Set I)).edgeFinset.card := by
  classical
  let label := (C.minorModel hA hB).branchLabel
  let Q := (C.graph B).induce (S:Set I)
  let embed (i : {i // i∈S}) : Option I := some i.val
  have hinj : Set.InjOn (Sym2.map label) (C.markedEdges B S) := by
    intro e he f hf heq
    obtain ⟨hei,i,hi,j,hj,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
    obtain ⟨hfi,k,hk,l,hl,u,hu,v,hv,rfl⟩ := Finset.mem_filter.mp hf
    have hxy : B.Adj x y := by simpa using hei
    have huv : B.Adj u v := by simpa using hfi
    simp only [Sym2.map_mk,label,(C.minorModel hA hB).branchLabel_eq hx,
      (C.minorModel hA hB).branchLabel_eq hy,(C.minorModel hA hB).branchLabel_eq hu,
      (C.minorModel hA hB).branchLabel_eq hv,Sym2.eq_iff,Option.some.injEq] at heq
    rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hsingle _ _ x hx y hy u hu v hv hxy huv
    · exact (hsingle _ _ x hx y hy v hv u hu hxy huv.symm).trans Sym2.eq_swap
  have hsub : (C.markedEdges B S).image (Sym2.map label) ⊆
      Q.edgeFinset.image (Sym2.map embed) := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hei,i,hi,j,hj,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
    have hxy : B.Adj x y := by simpa using hei
    have hne : i≠j := by
      intro heq
      subst j
      exact hloop i x hx y hy hxy
    refine Finset.mem_image.mpr ⟨s(⟨i,hi⟩,⟨j,hj⟩),?_,?_⟩
    · apply SimpleGraph.mem_edgeFinset.mpr
      exact ⟨hne,x,hx,y,hy,hxy⟩
    · simp only [Sym2.map_mk,embed,label,(C.minorModel hA hB).branchLabel_eq hx,
        (C.minorModel hA hB).branchLabel_eq hy]
  have hembed : Function.Injective embed := by
    intro i j h
    exact Subtype.ext (Option.some.inj h)
  calc
    _ = ((C.markedEdges B S).image (Sym2.map label)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Q.edgeFinset.image (Sym2.map embed)).card := Finset.card_le_card hsub
    _ = Q.edgeFinset.card := Finset.card_image_of_injective _ (Sym2.map.injective hembed)

/-- Weighted girth supplies both uniqueness conditions on the actual host,
so every selected original heavy edge is counted exactly once in the quotient. -/
theorem marked_edges_card_le_of_girth (C : ClusterFamily (I := I) A w D)
    (hA : A ≤ G) (hB : B ≤ G) (S : Finset I) {g L : ℝ}
    (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet, 0≤w e)
    (hlight : ∀ e∈A.edgeSet, w e < L) (hheavy : ∀ e∈B.edgeSet, L≤w e)
    (hg : 2≤g) (hD : 0≤D) (hL : 0<L) (hbudget : 2*D ≤ (g-2)*L) :
    (C.markedEdges B S).card ≤ ((C.graph B).induce (S:Set I)).edgeFinset.card := by
  classical
  have hbudget1 : D ≤ (g-1)*L := by nlinarith only [hD,hL.le,hbudget]
  apply C.marked_edges_card_le hA hB S
  · intro i x hx y hy hxy
    exact C.no_heavy_loop hA hG hw hlight (by linarith) hbudget1 i hx hy
      (hB hxy) (hheavy _ hxy)
  · intro i j x hx y hy u hu v hv hxy huv
    rcases le_total (w s(x,y)) (w s(u,v)) with hle | hle
    · exact C.heavy_edge_unique hA hG hw hlight hg hbudget i j hx hy hu hv
        (hB hxy) (hB huv) (hheavy _ huv) hle
    · exact (C.heavy_edge_unique hA hG hw hlight hg hbudget i j hu hv hx hy
        (hB huv) (hB hxy) (hheavy _ hxy) hle).symm

/-- All marked weights are original host weights. Their sum is bounded by
maximum edge weight times the proved original-edge count. -/
theorem marked_edges_weight_le (C : ClusterFamily (I := I) A w D)
    (S : Finset I) (M : ℝ) (hweight : ∀ e∈B.edgeSet, w e ≤ M) :
    (∑ e∈C.markedEdges B S, w e) ≤ (C.markedEdges B S).card*M := by
  classical
  calc
    _ ≤ ∑ _e∈C.markedEdges B S, M := Finset.sum_le_sum fun e he =>
      hweight e (SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp he).1)
    _ = _ := by simp

end ClusterFamily
end MinorFreeSpanners
