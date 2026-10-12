import MinorFreeSpanners.AssembledChargeLabels

/-! Every represented original heavy edge touching a residual old cluster is covered
by the actual charged labels. This uses exact empty unpaid-edge bags, rather
than a bound on a collapsed root quotient. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) B w D₀} {hB : B≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {roots : Finset I}
variable (O : ResidualOwnership H roots)
variable {d credit : I → ℝ} {M L c b a : ℝ} {spare future : {r // r∈roots} → ℝ} {N : ℕ}
variable (Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hB hT H hH
    (Finset.univ\roots) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N)

 theorem incident_residual_edge_mem_touching [Fintype V] (E : SimpleGraph V)
    (hcover : ∀ y,∃ j,y∈C.branch j) {i : I} (hi : i∉roots)
    {x y : V} (hx : x∈C.branch i) (hxy : E.Adj x y) :
    s(x,y)∈C.touchingEdges E (Finset.univ\roots) := by
  classical
  obtain ⟨j,hy⟩ := hcover y
  exact C.original_edge_mem_touching _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩) hx hy hxy

 theorem residual_touching_subset_charge [Fintype V] (E : SimpleGraph V)
    (active : Finset (Finset I)) (owner : {S // S∈active} → {r // r∈roots})
    (hempty : ∀ S∈leftovers O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q)=∅) :
    C.touchingEdges E (Finset.univ\roots)⊆C.touchingEdges E (chargeLabels O Q active owner) := by
  classical
  intro e he
  obtain ⟨hEe,i,hi,j,x,hx,y,hy,heq⟩ := Finset.mem_filter.mp he
  subst e
  have hxy : E.Adj x y := mem_edgeFinset.mp hEe
  have hcover : i∈(Finset.univ.biUnion (rootCarrier O Q))∪(leftovers O Q).biUnion id := by
    rw [(full_partition O Q).2.2.2.2.2]
    exact Finset.mem_univ _
  rcases Finset.mem_union.mp hcover with hiC | hiS
  · obtain ⟨r,_,hiC⟩ := Finset.mem_biUnion.mp hiC
    rcases Finset.mem_insert.mp hiC with hir | hid
    · exact ((Finset.mem_sdiff.mp hi).2 (hir ▸ r.property)).elim
    · exact C.original_edge_mem_touching _ (selected_subset_charge O Q active owner r hid) hx hy hxy
  · obtain ⟨S,hS,hiS⟩ := Finset.mem_biUnion.mp hiS
    by_cases hSa : S∈active
    · exact C.original_edge_mem_touching _ (active_subset_charge O Q active owner
        (Finset.mem_biUnion.mpr ⟨S,hSa,hiS⟩)) hx hy hxy
    · have hpaid : s(x,y)∈C.touchingEdges E (allPaidLabels O Q) := by
        by_contra hnot
        have hh : s(x,y)∈C.unpaidTouchingEdges E S (allPaidLabels O Q) :=
          Finset.mem_sdiff.mpr ⟨C.original_edge_mem_touching S hiS hx hy hxy,hnot⟩
        rw [hempty S hS hSa] at hh
        exact Finset.notMem_empty _ hh
      obtain ⟨heE,k,hk,l,u,hu,v,hv,he⟩ := Finset.mem_filter.mp hpaid
      rw [he]
      exact C.original_edge_mem_touching _ (allPaid_subset_charge O Q active owner hk) hu hv
        (mem_edgeFinset.mp (he ▸ heE))

 theorem residual_touching_weight_le [Fintype V] (E : SimpleGraph V) (hE : E≤G)
    (active : Finset (Finset I)) (hactive : active⊆leftovers O Q)
    (owner : {S // S∈active} → {r // r∈roots})
    (hempty : ∀ S∈leftovers O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q)=∅)
    (q : ℕ) (edgeMax : ℝ) (hMax : 0≤edgeMax)
    (hdeg : ∀ i∉roots,(C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e) (hw : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈C.touchingEdges E (Finset.univ\roots),w e)≤
      ((q:ℝ)*edgeMax)*(chargeLabels O Q active owner).card := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (residual_touching_subset_charge O Q E active owner hempty)
    (fun e he _ => hw0 e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1))).trans
      (C.touching_edges_weight_le hB hE _ q edgeMax hMax
        (fun i hi => hdeg i (Finset.mem_sdiff.mp (charge_subset_residual O Q active hactive owner hi)).2)
        hw hloop hsingle)

end AssembledPathFamilies
end MinorFreeSpanners
