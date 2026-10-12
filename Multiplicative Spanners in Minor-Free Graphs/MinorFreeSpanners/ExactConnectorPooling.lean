import MinorFreeSpanners.DisjointCreditPooling

/-! Retain the exact original unit-connector union in the pooled ledger.
Replacing it by the whole spanning tree loses the freshness information needed
for the multilevel potential. Disjoint old-label carriers identify both sums. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V J : Type*} [Fintype I] [Fintype J]
variable {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

noncomputable def connectorPool (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (S : J → Finset I) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.biUnion (fun j => C.connectorEdges hA hT (H j) (hH j) (S j))

 theorem disjoint_credit_pooling_exact (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (S : J → Finset I) (hS : ∀ i j,i≠j → Disjoint (S i) (S j))
    (credit : I → ℝ) (cost : J → ℝ) (c : ℝ)
    (hpaid : ∀ j,cost j≤(∑ i∈S j,credit i)+
      c*(∑ e∈C.connectorEdges hA hT (H j) (hH j) (S j),w e)) :
    (∑ j,cost j)≤(∑ i∈Finset.univ.biUnion S,credit i)+
      c*(∑ e∈C.connectorPool hA hT H hH S,w e) := by
  classical
  have hd : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint S :=
    fun i _ j _ hij => hS i j hij
  have he : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint
      (fun j => C.connectorEdges hA hT (H j) (hH j) (S j)) := by
    intro i _ j _ hij
    exact C.connectorEdges_disjoint_graphs hA hT (H i) (H j) (hH i) (hH j) (S i) (S j) (hS i j hij)
  have hh := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset J)) => hpaid j)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,connectorPool,Finset.sum_biUnion hd,
    Finset.sum_biUnion he] using hh

 theorem connectorPool_fresh (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (S : J → Finset I) {e : Sym2 V} (he : e∈C.connectorPool hA hT H hH S)
    (i : I) (x y : V) (hx : x∈C.branch i) (hy : y∈C.branch i) : e≠s(x,y) := by
  classical
  obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
  exact C.connectorEdges_fresh hA hT (H j) (hH j) (S j) he i x y hx hy

 theorem connectorPool_mem (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (S : J → Finset I) {e : Sym2 V} (he : e∈C.connectorPool hA hT H hH S) : e∈T.edgeSet := by
  classical
  obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
  exact C.connectorEdges_mem hA hT (H j) (hH j) (S j) he

end ClusterFamily
end MinorFreeSpanners
