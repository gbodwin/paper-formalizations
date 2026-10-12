import MinorFreeSpanners.MixedOriginalEdgeTransport
import MinorFreeSpanners.PriorPaidEdgeAlgebra

/-! Prior paid mixed roots expand to their actual old-label unions. Both the
paid and remaining edge bags retain literal original unordered host edges,
including multiple original incidences concealed by a collapsed root. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

noncomputable def originalMixedLabels {I : Type*} (P : Finset (Finset I))
    (S : Finset (SelectedResidualIndex P)) : Finset I := by
  classical
  exact S.biUnion (Sum.elim Subtype.val (fun i => {i.val}))

namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D D₁ : ℝ}

omit [Fintype I] [Fintype V] in
 theorem mixed_branch_original (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (j : SelectedResidualIndex P) (x : V) :
    x∈(C.selectedResidual hA P F hbranch).branch j ↔
      ∃ i∈Sum.elim Subtype.val (fun i => {i.val}) j,x∈C.branch i := by
  cases j with
  | inl S => exact Set.ext_iff.mp (hbranch S) x
  | inr i => simp [selectedResidual]

 theorem mixed_all_touching_edges_eq (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i) (S : Finset (SelectedResidualIndex P)) :
    (C.selectedResidual hA P F hbranch).touchingEdges B S=
      C.touchingEdges B (originalMixedLabels P S) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨hBe,j,hj,k,x,hx,y,_,rfl⟩ := Finset.mem_filter.mp he
    obtain ⟨i,hi,hx⟩ := (C.mixed_branch_original hA P F hbranch j x).mp hx
    obtain ⟨l,hy⟩ := hcover y
    exact C.original_edge_mem_touching _ (Finset.mem_biUnion.mpr ⟨j,hj,hi⟩) hx hy
      (mem_edgeFinset.mp hBe)
  · intro he
    obtain ⟨hBe,i,hi,j,x,hx,y,_,rfl⟩ := Finset.mem_filter.mp he
    obtain ⟨k,hk,hi⟩ := Finset.mem_biUnion.mp hi
    have hxk := (C.mixed_branch_original hA P F hbranch k x).mpr ⟨i,hi,hx⟩
    obtain ⟨l,hy⟩ := C.selectedResidual_covers hA P F hbranch hcover y
    exact (C.selectedResidual hA P F hbranch).original_edge_mem_touching _ hk hxk hy
      (mem_edgeFinset.mp hBe)

 theorem mixed_unpaid_edges_eq (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i) (S prior : Finset (SelectedResidualIndex P)) :
    (C.selectedResidual hA P F hbranch).unpaidTouchingEdges B S prior=
      C.unpaidTouchingEdges B (originalMixedLabels P S) (originalMixedLabels P prior) := by
  simp only [unpaidTouchingEdges,C.mixed_all_touching_edges_eq hA P F hbranch hcover]

 theorem mixed_prior_payment_partition (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i) (S prior : Finset (SelectedResidualIndex P)) :
    (∑ e∈C.touchingEdges B (originalMixedLabels P S),w e)=
      (∑ e∈C.touchingEdges B (originalMixedLabels P S)∩C.touchingEdges B (originalMixedLabels P prior),w e)+
      ∑ e∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges B S prior,w e := by
  rw [C.mixed_unpaid_edges_eq hA P F hbranch hcover]
  exact (C.original_touching_payment_partition (B:=B) (originalMixedLabels P S) (originalMixedLabels P prior)).2

end ClusterFamily
end MinorFreeSpanners
