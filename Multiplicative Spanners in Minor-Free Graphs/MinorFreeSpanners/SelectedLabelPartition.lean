import MinorFreeSpanners.PartitionQuotientForest
import MinorFreeSpanners.MixedPriorEdgeTransport

/-! The actual selected cluster unions and unchanged residual singletons form
one original-label partition. Its quotient edges lift to original unit-tree
edges between the same host branches. No selected set must be tree-connected. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} {A G T : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}

noncomputable def selectedLabelPartition (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) :
    LabelPartition I (SelectedResidualIndex P) where
  piece := fun j => {i | i∈Sum.elim Subtype.val (fun i => {i.val}) j}
  nonempty := by
    intro j
    cases j with
    | inl S =>
      obtain ⟨x,hx⟩ := F.nonempty S
      rw [hbranch] at hx
      obtain ⟨i,hi,_⟩ := hx
      exact ⟨i,hi⟩
    | inr i => exact ⟨i.val,by simp⟩
  disjoint := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro i hj hk
    obtain ⟨x,hx⟩ := C.nonempty i
    exact Set.disjoint_left.mp ((C.selectedResidual hA P F hbranch).disjoint j k hjk)
      ((C.mixed_branch_original hA P F hbranch j x).mpr ⟨i,hj,hx⟩)
      ((C.mixed_branch_original hA P F hbranch k x).mpr ⟨i,hk,hx⟩)
  covers := by
    classical
    intro i
    by_cases hi : i∈P.biUnion id
    · obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
      exact ⟨Sum.inl ⟨S,hS⟩,hi⟩
    · exact ⟨Sum.inr ⟨i,hi⟩,by simp⟩

 theorem selected_partition_singleton (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (i : {i // i∉P.biUnion id}) :
    (C.selectedLabelPartition hA P F hbranch).piece (Sum.inr i)={i.val} := by
  classical
  ext j
  simp [selectedLabelPartition]

 theorem selected_partition_quotient_le (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (K : SimpleGraph I) (hK : K≤C.graph T) :
    (C.selectedLabelPartition hA P F hbranch).graph K≤
      (C.selectedResidual hA P F hbranch).graph T := by
  rintro j k ⟨hne,i,hi,l,hl,hil⟩
  obtain ⟨_,x,hx,y,hy,hxy⟩ := hK hil
  exact ⟨hne,x,(C.mixed_branch_original hA P F hbranch j x).mpr ⟨i,hi,hx⟩,
    y,(C.mixed_branch_original hA P F hbranch k y).mpr ⟨l,hl,hy⟩,hxy⟩

 theorem exists_selected_residual_tree (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (K : SimpleGraph I) (hK : K.IsTree) (hKQ : K≤C.graph T) :
    ∃ H : SimpleGraph (SelectedResidualIndex P),
      H≤(C.selectedResidual hA P F hbranch).graph T ∧ H.IsTree ∧
      ∀ i j : {i // i∉P.biUnion id},H.Adj (Sum.inr i) (Sum.inr j) ↔ K.Adj i.val j.val := by
  classical
  let Q := C.selectedLabelPartition hA P F hbranch
  let R : Set (SelectedResidualIndex P) := Set.range Sum.inr
  have hs : ∀ j∈R,Q.piece j={Q.representative j} := by
    rintro _ ⟨i,rfl⟩
    have hp := Q.representative_mem (Sum.inr i)
    rw [C.selected_partition_singleton hA P F hbranch i] at hp
    have he : Q.representative (Sum.inr i)=i.val := hp
    rw [he]
    exact C.selected_partition_singleton hA P F hbranch i
  obtain ⟨H,hHQ,hH,heq⟩ := Q.exists_tree_preserving_singletons K hK R hs
  refine ⟨H,le_trans hHQ (C.selected_partition_quotient_le hA P F hbranch K hKQ),hH,?_⟩
  intro i j
  have he := congrArg (fun M : SimpleGraph (SelectedResidualIndex P) => M.Adj (Sum.inr i) (Sum.inr j)) heq
  have hh : H.Adj (Sum.inr i) (Sum.inr j) ↔ (Q.graph K).Adj (Sum.inr i) (Sum.inr j) := by
    simpa only [withinVertices,R,Set.mem_range_self,and_true] using Iff.of_eq he
  rw [hh]
  constructor
  · rintro ⟨_,x,hx,y,hy,hxy⟩
    rw [C.selected_partition_singleton hA P F hbranch i] at hx
    rw [C.selected_partition_singleton hA P F hbranch j] at hy
    have hx' : x=i.val := hx
    have hy' : y=j.val := hy
    subst x
    subst y
    exact hxy
  · intro hij
    refine ⟨?_,i.val,?_,j.val,?_,hij⟩
    · intro he
      exact hij.ne (congrArg Subtype.val (Sum.inr.inj he))
    · change i.val∈({i.val}:Finset I)
      simp
    · change j.val∈({j.val}:Finset I)
      simp

end ClusterFamily
end MinorFreeSpanners
