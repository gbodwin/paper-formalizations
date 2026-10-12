import MinorFreeSpanners.MarkedClusterEdges

/-! Low-degree payment counts every original heavy edge touching a selected
old cluster, including edges crossing to unselected old clusters. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
attribute [local instance] Classical.propDecidable

noncomputable def touchingEdges (C : ClusterFamily (I := I) A w D)
    (B : SimpleGraph V) (S : Finset I) : Finset (Sym2 V) := by
  classical
  exact B.edgeFinset.filter fun e =>
    ∃ i∈S, ∃ j, ∃ x∈C.branch i, ∃ y∈C.branch j, e=s(x,y)

 theorem touching_edges_card_le (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hB : B≤G) (S : Finset I)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j →
      B.Adj x y → B.Adj u v → s(x,y)=s(u,v)) :
    (C.touchingEdges B S).card≤∑ i∈S,(C.graph B).degree i := by
  classical
  let label := (C.minorModel hA hB).branchLabel
  let Q := C.graph B
  have hinj : Set.InjOn (Sym2.map label) (C.touchingEdges B S) := by
    intro e he f hf heq
    obtain ⟨hei,i,hi,j,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
    obtain ⟨hfi,k,hk,l,u,hu,v,hv,rfl⟩ := Finset.mem_filter.mp hf
    have hxy : B.Adj x y := by simpa using hei
    have huv : B.Adj u v := by simpa using hfi
    simp only [Sym2.map_mk,label,(C.minorModel hA hB).branchLabel_eq hx,
      (C.minorModel hA hB).branchLabel_eq hy,(C.minorModel hA hB).branchLabel_eq hu,
      (C.minorModel hA hB).branchLabel_eq hv,Sym2.eq_iff,Option.some.injEq] at heq
    rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hsingle _ _ x hx y hy u hu v hv hxy huv
    · exact (hsingle _ _ x hx y hy v hv u hu hxy huv.symm).trans Sym2.eq_swap
  have hsub : (C.touchingEdges B S).image (Sym2.map label) ⊆
      (S.biUnion (fun i => Q.incidenceFinset i)).image (Sym2.map some) := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hei,i,hi,j,x,hx,y,hy,rfl⟩ := Finset.mem_filter.mp he
    have hxy : B.Adj x y := by simpa using hei
    have hne : i≠j := by
      intro heq
      subst j
      exact hloop i x hx y hy hxy
    refine Finset.mem_image.mpr ⟨s(i,j),?_,?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨i,hi,?_⟩
      apply Q.mem_incidenceFinset.mpr
      apply Q.mk'_mem_incidenceSet_left_iff.mpr
      exact ⟨hne,x,hx,y,hy,hxy⟩
    · simp only [Sym2.map_mk,label,(C.minorModel hA hB).branchLabel_eq hx,
        (C.minorModel hA hB).branchLabel_eq hy]
  calc
    _ = ((C.touchingEdges B S).image (Sym2.map label)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((S.biUnion (fun i => Q.incidenceFinset i)).image (Sym2.map some)).card := Finset.card_le_card hsub
    _ = (S.biUnion (fun i => Q.incidenceFinset i)).card :=
      Finset.card_image_of_injective _ (Sym2.map.injective (@Option.some_injective I))
    _ ≤ ∑ i∈S,(Q.incidenceFinset i).card := Finset.card_biUnion_le
    _ = _ := by simp only [SimpleGraph.card_incidenceFinset_eq_degree,Q]

 theorem touching_edges_weight_le (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hB : B≤G) (S : Finset I) (q : ℕ) (M : ℝ) (hM : 0≤M)
    (hdeg : ∀ i∈S,(C.graph B).degree i≤q)
    (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j →
      B.Adj x y → B.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈C.touchingEdges B S,w e)≤((q:ℝ)*M)*S.card := by
  classical
  have hcount := C.touching_edges_card_le hA hB S hloop hsingle
  have hq : (C.touchingEdges B S).card≤S.card*q := by
    exact hcount.trans (by simpa using Finset.sum_le_sum fun i hi => hdeg i hi)
  have hqR : ((C.touchingEdges B S).card:ℝ)≤S.card*q := by exact_mod_cast hq
  calc
    _ ≤ ∑ _e∈C.touchingEdges B S,M := Finset.sum_le_sum fun e he =>
      hweight e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1)
    _ = (C.touchingEdges B S).card*M := by simp
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hqR hM]

end ClusterFamily
end MinorFreeSpanners
