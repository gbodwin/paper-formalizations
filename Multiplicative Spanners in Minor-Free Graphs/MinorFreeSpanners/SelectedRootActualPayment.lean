import MinorFreeSpanners.RootPaymentUnion
import MinorFreeSpanners.PriorPaidEdgeAlgebra
import MinorFreeSpanners.ExactConnectorPooling

/-! Actual touching-edge core payments combine with the actual marked high-root
bill on disjoint original old-label groups. No independent root-spending ledger
is postulated: it is obtained from these two kinds of preceding phase contract. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V J : Type*} [Fintype I] [Fintype V] [Fintype J]
variable {A T E G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

omit [Fintype J] in
 theorem touching_edges_biUnion (C : ClusterFamily (I:=I) A w D)
    (S : Finset J) (groups : J → Finset I) :
    C.touchingEdges E (S.biUnion groups)=S.biUnion (fun j => C.touchingEdges E (groups j)) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨he,i,hi,k,x,hx,y,hy,hee⟩ := Finset.mem_filter.mp he
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨he,i,hij,k,x,hx,y,hy,hee⟩⟩
  · intro he
    obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨he,i,hi,k,x,hx,y,hy,hee⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨he,i,Finset.mem_biUnion.mpr ⟨j,hj,hi⟩,k,x,hx,y,hy,hee⟩

 theorem selected_root_actual_payment (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (high : Finset J) (groups : J → Finset I)
    (hgroups : ∀ i j,i≠j → Disjoint (groups i) (groups j))
    (H : J → SimpleGraph I) (hH : ∀ j,H j≤C.graph T)
    (old : I → ℝ) (keep : J → ℝ) (c : ℝ) (hc : 0≤c)
    (hwT : ∀ e∈T.edgeSet,0≤w e)
    (hw : ∀ e∈E.edgeSet,0≤w e)
    (hhigh : (∑ e∈C.markedEdges E (high.biUnion groups),w e)+(∑ j∈high,keep j)≤
      (∑ j∈high,∑ i∈groups j,old i))
    (hweak : ∀ j,j∉high → (∑ e∈C.touchingEdges E (groups j),w e)+keep j≤
      (∑ i∈groups j,old i)+c*(∑ e∈C.connectorEdges hA hT (H j) (hH j) (groups j),w e)) :
    (∑ e∈C.markedEdges E (high.biUnion groups),w e)+
      (∑ e∈C.touchingEdges E ((Finset.univ\high).biUnion groups),w e)+(∑ j,keep j)≤
        (∑ i∈Finset.univ.biUnion groups,old i)+c*(∑ e∈C.connectorPool hA hT H hH groups,w e) := by
  classical
  have hbridge0 : 0≤c*(∑ j∈high,∑ e∈C.connectorEdges hA hT (H j) (hH j) (groups j),w e) :=
    mul_nonneg hc (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun e he =>
      hwT e (C.connectorEdges_mem hA hT (H j) (hH j) (groups j) he))
  have hhigh' := hhigh.trans (le_add_of_nonneg_right hbridge0)
  have hh := root_payment_union high (fun j => C.touchingEdges E (groups j)) w keep
    (fun j => ∑ i∈groups j,old i)
    (fun j => ∑ e∈C.connectorEdges hA hT (H j) (hH j) (groups j),w e)
    (∑ e∈C.markedEdges E (high.biUnion groups),w e) c
    (fun _ _ e he => hw e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1)) hhigh' hweak
  have hg : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint groups :=
    fun i _ j _ hij => hgroups i j hij
  have hb : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint
      (fun j => C.connectorEdges hA hT (H j) (hH j) (groups j)) :=
    fun i _ j _ hij => C.connectorEdges_disjoint_graphs hA hT (H i) (H j)
      (hH i) (hH j) (groups i) (groups j) (hgroups i j hij)
  rw [←Finset.sum_biUnion hg,←Finset.sum_biUnion hb] at hh
  simp only [connectorPool,C.touching_edges_biUnion]
  convert hh using 3
  congr 1
  ext e
  simp

end ClusterFamily
end MinorFreeSpanners
