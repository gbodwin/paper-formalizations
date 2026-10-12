import MinorFreeSpanners.RetainedConnectorInternality

/-! Turn the actual disjoint host carriers and intrinsic metric witnesses into
a covering cluster family, retaining literal old labels and connector edges. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I J V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D U : ℝ}

noncomputable def ofIntrinsicCarriers (C : ClusterFamily (I:=I) A w D)
    (S : J → Finset I) (hne : ∀ j,(S j).Nonempty)
    (hdis : ∀ j k,j≠k → Disjoint (S j) (S k)) (radius : J → ℝ) (hU : ∀ j,radius j≤U)
    (hwalk : ∀ j,∀ x∈{x | ∃ i∈S j,x∈C.branch i},∀ y∈{x | ∃ i∈S j,x∈C.branch i},
      ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈S j,z∈C.branch i) ∧ walkWeight w p≤radius j) :
    ClusterFamily (I:=J) G w U where
  branch := fun j => {x | ∃ i∈S j,x∈C.branch i}
  nonempty := by
    intro j
    obtain ⟨i,hi⟩ := hne j
    obtain ⟨x,hx⟩ := C.nonempty i
    exact ⟨x,i,hi,hx⟩
  disjoint := by
    intro j k hne
    apply Set.disjoint_left.mpr
    rintro x ⟨i,hi,hxi⟩ ⟨l,hl,hxl⟩
    have he : i=l := by
      by_contra hn
      exact Set.disjoint_left.mp (C.disjoint i l hn) hxi hxl
    subst l
    exact Finset.disjoint_left.mp (hdis j k hne) hi hl
  connected := by
    intro j x hx y hy
    obtain ⟨p,hp,hw⟩ := hwalk j x hx y hy
    exact ⟨p,hp,hw.trans (hU j)⟩

 theorem union_family_covers (C : ClusterFamily (I:=I) A w D)
    (F : ClusterFamily (I:=J) G w U) (S : J → Finset I)
    (hbranch : ∀ j,F.branch j={x | ∃ i∈S j,x∈C.branch i})
    (hC : ∀ x,∃ i,x∈C.branch i) (hS : ∀ i,∃ j,i∈S j) :
    ∀ x,∃ j,x∈F.branch j := by
  intro x
  obtain ⟨i,hi⟩ := hC x
  obtain ⟨j,hj⟩ := hS i
  exact ⟨j,by rw [hbranch];exact ⟨i,hj,hi⟩⟩

 theorem merged_internal_connector_union [Fintype I] [Fintype J]
    {T : SimpleGraph V} (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (F : ClusterFamily (I:=J) G w U) (S : J → Finset I)
    (hbranch : ∀ j,F.branch j={x | ∃ i∈S j,x∈C.branch i})
    (hS : ∀ i,∃ j,i∈S j) (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (prior : Finset (Sym2 V))
    (hinternal : ∀ e∈prior,∃ i x y,x∈C.branch i ∧ y∈C.branch i ∧ e=s(x,y)) :
    ∀ e∈prior∪C.connectorPool hA hT H hH S,
      ∃ j x y,x∈F.branch j ∧ y∈F.branch j ∧ e=s(x,y) := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · obtain ⟨i,x,y,hx,hy,heq⟩ := hinternal e he
    obtain ⟨j,hj⟩ := hS i
    exact ⟨j,x,y,by rw [hbranch];exact ⟨i,hj,hx⟩,
      by rw [hbranch];exact ⟨i,hj,hy⟩,heq⟩
  · obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x,y,hx,hy,heq⟩ := C.connectorEdges_endpoints hA hT (H j) (hH j) (S j) he
    exact ⟨j,x,y,by rw [hbranch];exact hx,by rw [hbranch];exact hy,heq⟩

end ClusterFamily
end MinorFreeSpanners
