import MinorFreeSpanners.AssembledPathFamilies
import MinorFreeSpanners.OriginalUnpaidEdgeClassification
import MinorFreeSpanners.RootedAssemblyCreditLedger

/-! Large retained blocks keep the payment certificate from the same actual
root-fiber assembly. This retains their edge allocations as well as intrinsic
credit when the smaller active blocks are subsequently absorbed elsewhere. -/
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

noncomputable def rootSpent (r : {r // r∈roots}) : ℝ :=
  a*((O.components r).biUnion (Q r).selected).card+(∑ t∈O.components r,a*((Q r).ends t).card)

 theorem root_ledger (r : {r // r∈roots})
    (hcredit : c*(d r.val-1)+spare r≤credit r.val) :
    rootSpent O Q r+c*(Q r).radius+future r≤(∑ i∈rootCarrier O Q r,credit i)+
      c*(∑ e∈C.connectorEdges hB hT (Q r).rootGraph (Q r).rootGraph_sub (rootCarrier O Q r),w e) := by
  exact (Q r).retained_root_credit_ledger
    (fun h => (Finset.mem_sdiff.mp h).2 r.property) hcredit

 theorem leftover_large_payment {S : Finset I} (hS : S∈leftovers O Q) (hsize : N<S.card) :
    ∃ radius : ℝ,0≤radius ∧ L-1≤radius ∧ radius≤2*L+M-1 ∧
      (∀ x∈{x | ∃ i∈S,x∈C.branch i},∀ y∈{x | ∃ i∈S,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈S,z∈C.branch i) ∧ walkWeight w p≤radius) ∧
      c*radius+a*S.card+c*b/2≤(∑ i∈S,credit i)+c*(∑ e∈C.connectorEdges hB hT H hH S,w e) := by
  classical
  obtain ⟨r,_,hS⟩ := Finset.mem_biUnion.mp hS
  exact (Q r).large_payment S hS hsize

noncomputable def smallBlocks : Finset (Finset I) := by
  classical
  exact (leftovers O Q).filter (fun S => S.card≤N)

 theorem smallBlocks_subset : smallBlocks O Q⊆leftovers O Q := Finset.filter_subset _ _

noncomputable def allPaidLabels : Finset I := by
  classical
  exact residualStepOneLabels Finset.univ (blocks O Q) (selected O Q) (ends O Q) N

 theorem large_subset_paid {S : Finset I} (hS : S∈leftovers O Q) (hsize : N<S.card) :
    S⊆allPaidLabels O Q := by
  classical
  obtain ⟨r,t,ht,hS⟩ := leftover_component O Q hS
  have hr : O.owner t=r := by simpa [ResidualOwnership.components] using ht
  have hblock : S∈blocks O Q t := by
    change S∈(Q (O.owner t)).blocks t
    rw [hr]
    exact hS
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨S,Finset.mem_filter.mpr ⟨hblock,hsize⟩,hi⟩)⟩

 theorem large_unpaid_empty {E : SimpleGraph V} [Fintype V]
    {S : Finset I} (hS : S∈leftovers O Q) (hsize : N<S.card) :
    C.unpaidTouchingEdges E S (allPaidLabels O Q)=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heS,henot⟩ := Finset.mem_sdiff.mp he
  obtain ⟨hEe,i,hi,j,x,hx,y,hy,heq⟩ := Finset.mem_filter.mp heS
  subst e
  exact henot (C.original_edge_mem_touching (allPaidLabels O Q)
    (large_subset_paid O Q hS hsize hi) hx hy (mem_edgeFinset.mp hEe))

end AssembledPathFamilies
end MinorFreeSpanners
