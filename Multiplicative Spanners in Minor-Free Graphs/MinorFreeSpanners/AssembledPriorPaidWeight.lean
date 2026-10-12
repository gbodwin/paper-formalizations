import MinorFreeSpanners.AssembledOriginalWeightPayment
import MinorFreeSpanners.PriorPaidEdgeAlgebra

/-! Previously paid original incidences are subtracted before residual charging.
Actual inactive-block exclusion for the enlarged paid set implies that every
remaining residual edge has a charged residual endpoint. No degree budget is
charged to a prior-paid root. -/
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

 theorem prior_unpaid_subset_charge [Fintype V] (E : SimpleGraph V) (prior : Finset I)
    (active : Finset (Finset I)) (owner : {S // S∈active} → {r // r∈roots})
    (hempty : ∀ S∈leftovers O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q∪prior)=∅) :
    C.unpaidTouchingEdges E (Finset.univ\roots) prior⊆C.touchingEdges E (chargeLabels O Q active owner) := by
  classical
  intro e he
  obtain ⟨he,hprior⟩ := Finset.mem_sdiff.mp he
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
        have hh : s(x,y)∈C.unpaidTouchingEdges E S (allPaidLabels O Q∪prior) :=
          Finset.mem_sdiff.mpr ⟨C.original_edge_mem_touching S hiS hx hy hxy,by
            rw [C.touching_edges_union]
            intro hu
            exact (Finset.mem_union.mp hu).elim hnot hprior⟩
        rw [hempty S hS hSa] at hh
        exact Finset.notMem_empty _ hh
      obtain ⟨heE,k,hk,l,u,hu,v,hv,he⟩ := Finset.mem_filter.mp hpaid
      rw [he]
      exact C.original_edge_mem_touching _ (allPaid_subset_charge O Q active owner hk) hu hv
        (mem_edgeFinset.mp (he ▸ heE))

 theorem prior_unpaid_weight_le [Fintype V] (E : SimpleGraph V) (hE : E≤G) (prior : Finset I)
    (active : Finset (Finset I)) (hactive : active⊆leftovers O Q)
    (owner : {S // S∈active} → {r // r∈roots})
    (hempty : ∀ S∈leftovers O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q∪prior)=∅)
    (q : ℕ) (edgeMax : ℝ) (hMax : 0≤edgeMax)
    (hdeg : ∀ i∉roots,(C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e) (hw : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈C.unpaidTouchingEdges E (Finset.univ\roots) prior,w e)≤
      ((q:ℝ)*edgeMax)*(chargeLabels O Q active owner).card := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (prior_unpaid_subset_charge O Q E prior active owner hempty)
    (fun e he _ => hw0 e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1))).trans
      (C.touching_edges_weight_le hB hE _ q edgeMax hMax
        (fun i hi => hdeg i (Finset.mem_sdiff.mp (charge_subset_residual O Q active hactive owner hi)).2)
        hw hloop hsingle)

 theorem prior_unpaid_weight_payment [Fintype V] (E : SimpleGraph V) (hE : E≤G) (prior : Finset I)
    (active : Finset (Finset I)) (hactive : active⊆smallBlocks O Q)
    (owner : {S // S∈active} → {r // r∈roots})
    (hempty : ∀ S∈leftovers O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q∪prior)=∅)
    (q : ℕ) (edgeMax : ℝ) (hMax : 0≤edgeMax) (ha : 0≤a) (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i∉roots,(C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e) (hw : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈C.unpaidTouchingEdges E (Finset.univ\roots) prior,w e)≤
      (∑ r,(rootSpent O Q r+a*(assignedBlockUnion active owner r).card))+
      ∑ S : {S // S∈leftovers O Q\active},(if N<S.val.card then a*S.val.card else 0) := by
  have hbound := (prior_unpaid_weight_le O Q E hE prior active
    (hactive.trans (smallBlocks_subset O Q)) owner hempty q edgeMax hMax hdeg hw0 hw hloop hsingle).trans
      (mul_le_mul_of_nonneg_right hqa (Nat.cast_nonneg _))
  have hb := hbound.trans (charge_budget O Q active owner ha)
  simpa only [large_allocation_eq_inactive O Q active hactive] using hb

end AssembledPathFamilies
end MinorFreeSpanners
