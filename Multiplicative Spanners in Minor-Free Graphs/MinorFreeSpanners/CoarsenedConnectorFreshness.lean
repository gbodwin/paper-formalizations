import MinorFreeSpanners.ExactConnectorPooling

/-! Literal connector freshness survives whole-branch coarsening. A connector
chosen across a coarser family cannot reuse an earlier edge internal to an
original branch. This does not assert that an arbitrary phase output exposes
its exact connector witnesses; that separate construction obligation remains. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset

 theorem internal_edges_of_coarsening {I J V : Type*}
    {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (F : ClusterFamily (I:=J) G w E)
    (hcoarse : ∀ i,∃ j,C.branch i⊆F.branch j) (prior : Finset (Sym2 V))
    (hprior : ∀ e∈prior,∃ i x y,x∈C.branch i ∧ y∈C.branch i ∧ e=s(x,y)) :
    ∀ e∈prior,∃ j x y,x∈F.branch j ∧ y∈F.branch j ∧ e=s(x,y) := by
  intro e he
  obtain ⟨i,x,y,hx,hy,heq⟩ := hprior e he
  obtain ⟨j,hj⟩ := hcoarse i
  exact ⟨j,x,y,hj hx,hj hy,heq⟩

 theorem coarsened_connectorPool_fresh {I J K V : Type*} [Fintype J] [Fintype K]
    {A G T : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (F : ClusterFamily (I:=J) G w E)
    (hcoarse : ∀ i,∃ j,C.branch i⊆F.branch j) (hT : T≤G)
    (H : K → SimpleGraph J) (hH : ∀ k,H k≤F.graph T) (S : K → Finset J)
    {e : Sym2 V} (he : e∈F.connectorPool le_rfl hT H hH S)
    (i : I) (x y : V) (hx : x∈C.branch i) (hy : y∈C.branch i) : e≠s(x,y) := by
  obtain ⟨j,hj⟩ := hcoarse i
  exact F.connectorPool_fresh le_rfl hT H hH S he j x y (hj hx) (hj hy)

 theorem coarsened_connectorPool_disjoint_history {I J K V : Type*} [Fintype J] [Fintype K]
    {A G T : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (F : ClusterFamily (I:=J) G w E)
    (hcoarse : ∀ i,∃ j,C.branch i⊆F.branch j) (hT : T≤G)
    (H : K → SimpleGraph J) (hH : ∀ k,H k≤F.graph T) (S : K → Finset J)
    (prior : Finset (Sym2 V))
    (hprior : ∀ e∈prior,∃ i x y,x∈C.branch i ∧ y∈C.branch i ∧ e=s(x,y)) :
    Disjoint prior (F.connectorPool le_rfl hT H hH S) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hn
  obtain ⟨i,x,y,hx,hy,heq⟩ := hprior e he
  exact coarsened_connectorPool_fresh C F hcoarse hT H hH S hn i x y hx hy heq

end MinorFreeSpanners
