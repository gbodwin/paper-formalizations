import MinorFreeSpanners.AssembledResidualEdgeCoverage
import MinorFreeSpanners.AssembledChargeBudget

/-! Original residual heavy-edge weight is paid by precisely the selected,
endpoint, active-block and large-leftover allocations. The degree bound is on
original old clusters, before roots are collapsed or heavy edges are absorbed. -/
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

 theorem large_allocation_eq_inactive (active : Finset (Finset I))
    (hactive : active⊆smallBlocks O Q) :
    (∑ S∈largeLeftovers O Q,a*S.card)=
      ∑ S : {S // S∈leftovers O Q\active},(if N<S.val.card then a*S.val.card else 0) := by
  classical
  have he : (leftovers O Q\active).filter (fun S => N<S.card)=largeLeftovers O Q := by
    ext S
    simp only [Finset.mem_filter,Finset.mem_sdiff,largeLeftovers]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · intro h
      refine ⟨⟨h.1,?_⟩,h.2⟩
      intro hS
      have hh := (Finset.mem_filter.mp (hactive hS)).2
      omega
  rw [←Finset.sum_subtype (leftovers O Q\active) (fun _ => Iff.rfl)
    (fun S => if N<S.card then a*S.card else 0),←Finset.sum_filter,he]

 theorem original_weight_payment [Fintype V] (E : SimpleGraph V) (hE : E≤G)
    (active : Finset (Finset I)) (hactive : active⊆smallBlocks O Q)
    (owner : {S // S∈active} → {r // r∈roots})
    (hempty : ∀ S∈leftovers O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q)=∅)
    (q : ℕ) (edgeMax : ℝ) (hMax : 0≤edgeMax) (ha : 0≤a) (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i∉roots,(C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e) (hw : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈C.touchingEdges E (Finset.univ\roots),w e)≤
      (∑ r,(rootSpent O Q r+a*(assignedBlockUnion active owner r).card))+
      ∑ S : {S // S∈leftovers O Q\active},(if N<S.val.card then a*S.val.card else 0) := by
  have hbound := (residual_touching_weight_le O Q E hE active
    (hactive.trans (smallBlocks_subset O Q)) owner hempty q edgeMax hMax hdeg hw0 hw hloop hsingle).trans
      (mul_le_mul_of_nonneg_right hqa (Nat.cast_nonneg _))
  have hb := hbound.trans (charge_budget O Q active owner ha)
  simpa only [large_allocation_eq_inactive O Q active hactive] using hb

end AssembledPathFamilies
end MinorFreeSpanners
