import MinorFreeSpanners.OriginalUnpaidEdgeClassification

/-! The actual degree-two residual forest selects its own spanning paths,
blocks and endpoint sets around the supplied actual ports. Its unallocated original heavy edges are
then proved to reach retained roots after literal previous payments. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem exists_actual_residual_heavy_classification
    (C : ClusterFamily (I := I) A w D)
    (H : SimpleGraph I) (hforest : H.IsAcyclic) (d : I → ℝ) (L M : ℝ)
    (W U R : Finset I) (hRW : R⊆W) (hRU : Disjoint R U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L B S ∧ ¬C.FourArmCore H d L B S)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent) (N : ℕ)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (hport : ∀ t∈F,port t∈ResidualComponents.block H R t)
    (hM : 0≤M) (hL : 0<L)
    (hdeg : ∀ i∈R,((H.neighborFinset i)∩R).card≤2)
    (hd0 : ∀ i∈W,0≤d i+1) (hd : ∀ i∈W,d i≤D)
    (hdM : ∀ i∈R,d i+1≤M)
    (hm : ∀ t∈F,L≤∑ i∈ResidualComponents.block H R t,(d i+1))
    (priorPaid roots : Finset I)
    (hcover : ∀ i,i∈F.biUnion (ResidualComponents.block H R) ∨ i∈priorPaid ∨ i∈roots) :
    ∃ P : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I),
    ∃ selected ends : (H.induce (R:Set I)).ConnectedComponent → Finset I,
      (∀ t∈F,ResidualAttachmentPartition H R t (fun i => d i+1)
        M L N (port t) (P t) (selected t) (ends t)) ∧
      let residual := F.biUnion (ResidualComponents.block H R)
      let paid := priorPaid ∪ residualStepOneLabels F P selected ends N
      (∀ e∈C.unpaidTouchingEdges B residual paid,
        ∃ i∈residual\paid,∃ j∈roots\paid,∃ x∈C.branch i,∃ y∈C.branch j,
          B.Adj x y ∧ e=s(x,y)) ∧
      Disjoint (C.unpaidTouchingEdges B residual paid)
        (C.touchingEdges B residual∩C.touchingEdges B paid) ∧
      (∑ e∈C.touchingEdges B residual,w e)=
        (∑ e∈C.touchingEdges B residual∩C.touchingEdges B paid,w e)+
        ∑ e∈C.unpaidTouchingEdges B residual paid,w e := by
  classical
  obtain ⟨P,selected,ends,hpart,_⟩ := exists_selected_residual_path_slices H hforest R F
    (fun i => d i+1) M L hM hL hdeg hdM hm port hport N
  refine ⟨P,selected,ends,hpart,?_,?_⟩
  · intro e he
    apply C.unpaid_original_edge_reaches_root _ _ roots ?_ ?_ he
    · intro i
      rcases hcover i with hi | hi | hi
      · exact Or.inl hi
      · exact Or.inr (Or.inl (Finset.mem_union_left _ hi))
      · exact Or.inr (Or.inr hi)
    · intro i hi j hj hip hjp x hx y hy
      exact C.no_unpaid_residual_edge H hforest d L M W U R hRW hRU hmax
        F N port P selected ends hpart hL hd0 hd hi hj
        (fun h => hip (Finset.mem_union_right _ h))
        (fun h => hjp (Finset.mem_union_right _ h)) hx hy
  · exact C.original_touching_payment_partition _ _

end ClusterFamily
end MinorFreeSpanners
