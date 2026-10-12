import MinorFreeSpanners.RootedPathAssemblyResult
import MinorFreeSpanners.FinitePartitionRefinement

/-! A connected original forest chooses every residual component's root and
actual boundary port internally. The full weighted one-root constructions
then simultaneously produce a disjoint covering output partition, retaining
all short interior blocks and every local original-host credit certificate. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem exists_multi_root_path_assembly {I V : Type*} [Fintype I]
    {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
    (C : ClusterFamily (I:=I) B w D₀) (hB : B≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (hforest : H.IsAcyclic) (hconn : ConnectedWithin H Finset.univ)
    (roots : Finset I) (hroots : roots.Nonempty)
    (d credit : I → ℝ) (M L c b a : ℝ) (spare future : {r // r∈roots} → ℝ) (N : ℕ)
    (hM : 0≤M) (hL : 0<L) (hroot : ∀ r∈roots,1≤d r) (hc : 0≤c) (ha : 0≤a)
    (hdeg : ∀ i∉roots,((H.neighborFinset i)\roots).card≤2)
    (hd : ∀ i∉roots,2≤d i) (hdM : ∀ i∉roots,d i≤M)
    (hm : ∀ t : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent,
      L≤∑ i∈ResidualComponents.block H (Finset.univ\roots) t,d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : B.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i-1)
    (hcredit : ∀ i∉roots,c*(d i-1)≤credit i) (hbase : ∀ i∉roots,c*b≤credit i)
    (hsize : 2*(2*L+M)≤N*b) (hhalf : 2*a≤c*b)
    (hdonor : 2*(N:ℝ)*a≤c*L/4) (hbudget : ∀ r,5*(N:ℝ)*a+future r≤spare r)
    (hcost : (N+1:ℕ)*a≤c*b/2) :
    ∃ O : ResidualOwnership H roots,
    ∃ Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hB hT H hH
      (Finset.univ\roots) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N,
      let output := Finset.univ.biUnion fun r => (Q r).output
      (∀ S∈output,S.Nonempty) ∧
      (∀ S∈output,∀ U∈output,S≠U → Disjoint S U) ∧
      output.biUnion id=Finset.univ ∧
      (∀ r s,r≠s → Disjoint (Q r).output (Q s).output) := by
  classical
  obtain ⟨O⟩ := exists_residual_ownership H hconn roots hroots
  have hbuild (r : {r // r∈roots}) : Nonempty (RootedPathAssemblyResult C hB hT H hH
      (Finset.univ\roots) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N) := by
    apply exists_rooted_path_assembly_result C hB hT hunit H hH hforest (Finset.univ\roots)
      r.val (fun h => (Finset.mem_sdiff.mp h).2 r.property) (O.components r) O.port
      (fun t _ => O.port_mem t) ?_ d credit M L c b a (spare r) (future r) N
      hM hL (hroot r.val r.property) hc ha ?_ ?_ ?_ (fun t _ => hm t) hdiam
      ?_ ?_ hsize hhalf hdonor (hbudget r) hcost
    · intro t ht
      have he : O.owner t=r := by simpa [ResidualOwnership.components] using ht
      simpa only [he] using hH (O.adjacent t)
    · intro i hi
      have he : H.neighborFinset i∩(Finset.univ\roots)=H.neighborFinset i\roots := by
        ext x;simp
      rw [he]
      exact hdeg i (Finset.mem_sdiff.mp hi).2
    · intro i hi;exact hd i (Finset.mem_sdiff.mp hi).2
    · intro i hi;exact hdM i (Finset.mem_sdiff.mp hi).2
    · intro i hi;exact hcredit i (Finset.mem_sdiff.mp hi).2
    · intro i hi;exact hbase i (Finset.mem_sdiff.mp hi).2
  let Q := fun r : {r // r∈roots} => Classical.choice (hbuild r)
  have href := finite_partition_refinement O.filled (fun r => (Q r).output)
    O.filled_disjoint (fun r => (Q r).output_union) (fun r => (Q r).output_ne)
    (fun r => (Q r).output_pairwise)
  have hfull : Finset.univ.biUnion O.filled=Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    obtain ⟨r,hr⟩ := O.filled_covers i
    exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ r,hr⟩
  exact ⟨O,Q,href.1,href.2.1,href.2.2.1.trans hfull,href.2.2.2⟩

end MinorFreeSpanners
