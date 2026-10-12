import MinorFreeSpanners.MultiRootPathAssembly
import MinorFreeSpanners.DisjointCreditPooling

/-! The simultaneous actual root assemblies spend each original old-vertex
credit and each original unit connector at most once. Root slack is charged
to that root's actual supplied credit before the pooled inequality is formed. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem rooted_assembly_pooled_payment {I V : Type*} [Fintype I] [Fintype V]
    {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
    (C : ClusterFamily (I:=I) B w D₀) (hB : B≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (roots : Finset I) (O : ResidualOwnership H roots)
    (d credit : I → ℝ) (M L c b a : ℝ) (spare future : {r // r∈roots} → ℝ) (N : ℕ)
    (Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hB hT H hH
      (Finset.univ\roots) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N)
    (hc : 0≤c) (hcredit : ∀ i,0≤credit i)
    (hrootcredit : ∀ r,c*(d r.val-1)+spare r≤credit r.val) :
    (∑ r : {r // r∈roots},(c*(Q r).radius+a*((O.components r).biUnion (Q r).selected).card+
      (∑ t∈O.components r,a*((Q r).ends t).card)+future r))≤
      (∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e) := by
  classical
  let S := fun r : {r // r∈roots} => insert r.val ((O.components r).biUnion (Q r).selected)
  have hsub (r : {r // r∈roots}) : ((O.components r).biUnion (Q r).selected)⊆O.absorbed r := by
    intro i hi
    obtain ⟨t,ht,hi⟩ := Finset.mem_biUnion.mp hi
    apply (O.mem_absorbed r i).mpr
    refine ⟨t,?_,?_⟩
    · simpa [ResidualOwnership.components] using ht
    · rw [←((Q r).partition t ht).cover]
      exact Finset.mem_biUnion.mpr ⟨(Q r).selected t,((Q r).partition t ht).member,hi⟩
  have hS (r : {r // r∈roots}) : S r⊆O.filled r := by
    exact Finset.insert_subset_insert r.val (hsub r)
  have hd : ∀ r s,r≠s → Disjoint (S r) (S s) :=
    fun r s hrs => (O.filled_disjoint r s hrs).mono (hS r) (hS s)
  apply C.disjoint_credit_pooling hB hT (fun r => (Q r).rootGraph)
    (fun r => (Q r).rootGraph_sub) S hd credit _ c hc hcredit
    (fun e he => by rw [hunit e he];norm_num)
  intro r
  have hnot : r.val∉(O.components r).biUnion (Q r).selected :=
    fun h => O.root_not_absorbed r r (hsub r h)
  have hs : (∑ i∈S r,credit i)=credit r.val+∑ i∈(O.components r).biUnion (Q r).selected,credit i :=
    Finset.sum_insert hnot
  rw [hs]
  have hp := (Q r).root_payment
  have hr := hrootcredit r
  dsimp [S]
  linarith

end MinorFreeSpanners
