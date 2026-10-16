import LightEFTSpanners.NativePartitionCriterion
import LightEFTSpanners.NativeCorePartitionBudget

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V E I : Type*} [Fintype E] [Fintype I]
attribute [local instance] Classical.propDecidable

omit [Fintype I] in
/-- The original identities crossing a partition inside the induced core are
exactly the internal crossing identities after complement contraction. The
outside vertex and its loops do not enter the actual induced core. -/
theorem induced_core_crossings_eq (G : Graph V E) (K : Set V)
    (assign : K → I) :
    actualPartitionCrossings (G.induce K) assign=
      partitionCrossings (G.map (collapseOutside K)) (Option.map assign) := by
  classical
  ext e
  simp only [actualPartitionCrossings,partitionCrossings,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,b,he,hab⟩
    have hm : (G.map (collapseOutside K)).IsLink e (some a) (some b) := by
      refine ⟨(a:V),(b:V),he.1,?_,?_⟩
      · unfold collapseOutside
        split
        · rfl
        · rename_i h
          exact False.elim (h a.property)
      · unfold collapseOutside
        split
        · rfl
        · rename_i h
          exact False.elim (h b.property)
    exact ⟨some a,some b,assign a,assign b,hm,rfl,rfl,hab⟩
  · rintro ⟨u,v,i,j,⟨x,y,hxy,rfl,rfl⟩,hi,hj,hij⟩
    have hx : x∈K := by
      by_contra hx
      simp [collapseOutside,hx] at hi
    have hy : y∈K := by
      by_contra hy
      simp [collapseOutside,hy] at hj
    let a : K := ⟨x,hx⟩
    let b : K := ⟨y,hy⟩
    have ha : assign a=i := by simpa [a,collapseOutside,hx] using hi
    have hb : assign b=j := by simpa [b,collapseOutside,hy] using hj
    refine ⟨a,b,⟨hxy,hx,hy⟩,?_⟩
    intro heq
    exact hij (ha.symm.trans (heq.trans hb))

omit [Fintype I] in
/-- The minimal-core cut argument supplies the genuine tree-partition
criterion on an actual induced native subgraph. The original-vertex inclusion
is explicit, and empty/singleton partition budgets are proved separately.
This prepares the premise of tree packing; it does not assume that theorem. -/
theorem native_core_treePartitionCriterion [Fintype V] (G : Graph V E)
    (K : Finset V) {k : ℕ} (hactual : (K:Set V)⊆G.vertexSet)
    (hsmall : (G.edgeCut (K:Set V)).toFinset.card≤2*k)
    (hmin : ∀ A : Finset V,A⊂K → A.Nonempty →
      2*k≤(G.edgeCut (A:Set V)).toFinset.card) :
    G.induce (K:Set V)≤G ∧ TreePartitionCriterion (G.induce (K:Set V)) k := by
  refine ⟨G.induce_le hactual,?_⟩
  intro m assign hsurj
  by_cases hm : m≤1
  · have hz : m-1=0 := by omega
    simp [hz]
  · have hm1 : 1<m := by omega
    let : Nontrivial (Fin m) := ⟨⟨⟨0,by omega⟩,⟨1,hm1⟩,by
      intro h
      have heq := congrArg Fin.val h
      simp at heq⟩⟩
    have hcount := native_minimal_core_partition_budget G K hsmall hmin assign hsurj
    rw [← induced_core_crossings_eq G (K:Set V) assign] at hcount
    simpa using hcount
end LightEFTSpanners.MultigraphCuts
