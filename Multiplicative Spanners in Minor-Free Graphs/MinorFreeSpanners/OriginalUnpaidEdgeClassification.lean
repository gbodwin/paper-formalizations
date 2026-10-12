import MinorFreeSpanners.ResidualUnpaidLabels
import MinorFreeSpanners.TouchingClusterEdges

/-! Classification retains each original unordered heavy-edge identity.
Subtracting paid old-label incidences leaves only edges to retained roots;
no degree of a collapsed root quotient is used. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem original_edge_mem_touching (C : ClusterFamily (I := I) A w D)
    (S : Finset I) {i j : I} (hi : i∈S)
    {x y : V} (hx : x∈C.branch i) (hy : y∈C.branch j) (hxy : B.Adj x y) :
    s(x,y)∈C.touchingEdges B S := by
  classical
  exact Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr hxy,i,hi,j,x,hx,y,hy,rfl⟩

noncomputable def unpaidTouchingEdges (C : ClusterFamily (I := I) A w D)
    (B : SimpleGraph V) (R paid : Finset I) : Finset (Sym2 V) := by
  classical
  exact C.touchingEdges B R \ C.touchingEdges B paid

 theorem unpaid_original_edge_reaches_root (C : ClusterFamily (I := I) A w D)
    (R paid roots : Finset I)
    (hcover : ∀ i,i∈R ∨ i∈paid ∨ i∈roots)
    (hno : ∀ i∈R,∀ j∈R,i∉paid → j∉paid →
      ∀ x∈C.branch i,∀ y∈C.branch j,¬B.Adj x y)
    {e : Sym2 V} (he : e∈C.unpaidTouchingEdges B R paid) :
    ∃ i∈R\paid,∃ j∈roots\paid,∃ x∈C.branch i,∃ y∈C.branch j,
      B.Adj x y ∧ e=s(x,y) := by
  classical
  obtain ⟨heR,henot⟩ := Finset.mem_sdiff.mp he
  obtain ⟨hBe,i,hi,j,x,hx,y,hy,heq⟩ := Finset.mem_filter.mp heR
  subst e
  have hxy : B.Adj x y := mem_edgeFinset.mp hBe
  have hip : i∉paid := fun h => henot (C.original_edge_mem_touching paid h hx hy hxy)
  have hjp : j∉paid := by
    intro h
    apply henot
    have hh := C.original_edge_mem_touching paid h hy hx hxy.symm
    simpa only [Sym2.eq_swap] using hh
  have hjroot : j∈roots := by
    rcases hcover j with hj | hj | hj
    · exact (hno i hi j hj hip hjp x hx y hy hxy).elim
    · exact (hjp hj).elim
    · exact hj
  exact ⟨i,Finset.mem_sdiff.mpr ⟨hi,hip⟩,j,Finset.mem_sdiff.mpr ⟨hjroot,hjp⟩,
    x,hx,y,hy,hxy,rfl⟩

 theorem unpaid_touching_subset (C : ClusterFamily (I := I) A w D)
    (R paid : Finset I) : C.unpaidTouchingEdges B R paid⊆C.touchingEdges B (R\paid) := by
  classical
  intro e he
  obtain ⟨heR,henot⟩ := Finset.mem_sdiff.mp he
  obtain ⟨hBe,i,hi,j,x,hx,y,hy,heq⟩ := Finset.mem_filter.mp heR
  subst e
  have hip : i∉paid := fun h => henot
    (C.original_edge_mem_touching paid h hx hy (mem_edgeFinset.mp hBe))
  exact C.original_edge_mem_touching (R\paid) (Finset.mem_sdiff.mpr ⟨hi,hip⟩)
    hx hy (mem_edgeFinset.mp hBe)

 theorem unpaid_touching_weight_le (C : ClusterFamily (I := I) A w D)
    (hA : A≤G) (hB : B≤G) (R paid : Finset I) (q : ℕ) (M : ℝ) (hM : 0≤M)
    (hw : ∀ e∈B.edgeSet,0≤w e)
    (hdeg : ∀ i∈R\paid,(C.graph B).degree i≤q)
    (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j →
      B.Adj x y → B.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈C.unpaidTouchingEdges B R paid,w e)≤((q:ℝ)*M)*(R\paid).card := by
  have hsub := C.unpaid_touching_subset (B:=B) R paid
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e he _ =>
    hw e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1))).trans
    (C.touching_edges_weight_le hA hB (R\paid) q M hM hdeg hweight hloop hsingle)

 theorem original_touching_payment_partition (C : ClusterFamily (I := I) A w D)
    (R paid : Finset I) :
    Disjoint (C.unpaidTouchingEdges B R paid) (C.touchingEdges B R∩C.touchingEdges B paid) ∧
    (∑ e∈C.touchingEdges B R,w e)=
      (∑ e∈C.touchingEdges B R∩C.touchingEdges B paid,w e)+
      ∑ e∈C.unpaidTouchingEdges B R paid,w e := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 (Finset.mem_inter.mp hf).2
  · exact (Finset.sum_inter_add_sum_sdiff (C.touchingEdges B R) (C.touchingEdges B paid) w).symm

end ClusterFamily
end MinorFreeSpanners
