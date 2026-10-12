import MinorFreeSpanners.ExpandedLabelPartition

/-! Extend the exact surviving-singleton forest in the quotient of the actual
previous mixed tree. This keeps every remaining residual edge and invents none,
even when selected root pieces are not connected in that previous tree. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I J V : Type*} [Fintype I] [Fintype J]
variable {A G T : SimpleGraph V} {w : Sym2 V → ℝ} {D E E' : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem exists_expanded_residual_tree (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={g // g∈P}) G w E)
    (hbranch : ∀ g,F.branch g={x | ∃ i∈g.val,x∈C.branch i})
    (S : J → Finset (SelectedResidualIndex P)) (hroot : selectedRoots P⊆Finset.univ.biUnion S)
    (Fnew : ClusterFamily (I:=J) G w E')
    (hnew : ∀ j,Fnew.branch j={x | ∃ i∈S j,x∈(C.selectedResidual hA P F hbranch).branch i})
    (U : Finset (Finset I)) (hU : U.biUnion id=originalMixedLabels P (Finset.univ.biUnion S))
    (e : J ≃ {g // g∈U})
    (hfinal : ∀ g,(Fnew.reindex e.symm).branch g={x | ∃ i∈g.val,x∈C.branch i})
    (K : SimpleGraph (SelectedResidualIndex P)) (hK : K.IsTree)
    (hKQ : K≤(C.selectedResidual hA P F hbranch).graph T) :
    ∃ H : SimpleGraph (SelectedResidualIndex U),
      H≤(C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).graph T ∧ H.IsTree ∧
      ∀ i j : {i // i∉U.biUnion id},H.Adj (Sum.inr i) (Sum.inr j) ↔
        K.Adj (Sum.inr (expandedResidualLabel P S hroot U hU i))
          (Sum.inr (expandedResidualLabel P S hroot U hU j)) := by
  classical
  let Q := C.expandedLabelPartition hA P F hbranch S hroot Fnew hnew U hU e hfinal
  let R : Set (SelectedResidualIndex U) := Set.range Sum.inr
  have hsingle (i : {i // i∉U.biUnion id}) :
      Q.piece (Sum.inr i)={Sum.inr (expandedResidualLabel P S hroot U hU i)} := rfl
  have hs : ∀ j∈R,Q.piece j={Q.representative j} := by
    rintro _ ⟨i,rfl⟩
    have hp := Q.representative_mem (Sum.inr i)
    rw [hsingle] at hp
    have he : Q.representative (Sum.inr i)=Sum.inr (expandedResidualLabel P S hroot U hU i) := hp
    rw [he]
    exact hsingle i
  obtain ⟨H,hHQ,hH,heq⟩ := Q.exists_tree_preserving_singletons K hK R hs
  have hQ : Q.graph K≤(C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).graph T := by
    rintro j k ⟨hne,i,hi,l,hl,hil⟩
    obtain ⟨_,x,hx,y,hy,hxy⟩ := hKQ hil
    exact ⟨hne,x,(C.expanded_piece_branch hA P F hbranch S hroot Fnew hnew U hU e hfinal j x).mpr ⟨i,hi,hx⟩,
      y,(C.expanded_piece_branch hA P F hbranch S hroot Fnew hnew U hU e hfinal k y).mpr ⟨l,hl,hy⟩,hxy⟩
  refine ⟨H,le_trans hHQ hQ,hH,?_⟩
  intro i j
  have he := congrArg (fun M : SimpleGraph (SelectedResidualIndex U) => M.Adj (Sum.inr i) (Sum.inr j)) heq
  have hh : H.Adj (Sum.inr i) (Sum.inr j) ↔ (Q.graph K).Adj (Sum.inr i) (Sum.inr j) := by
    simpa only [withinVertices,R,Set.mem_range_self,and_true] using Iff.of_eq he
  rw [hh]
  constructor
  · rintro ⟨_,x,hx,y,hy,hxy⟩
    rw [hsingle] at hx hy
    have hx' : x=Sum.inr (expandedResidualLabel P S hroot U hU i) := hx
    have hy' : y=Sum.inr (expandedResidualLabel P S hroot U hU j) := hy
    subst x
    subst y
    exact hxy
  · intro hij
    refine ⟨?_,_,?_,_,?_,hij⟩
    · intro he
      have he' : i=j := Sum.inr.inj he
      subst j
      exact hij.ne rfl
    · exact Set.mem_singleton _
    · exact Set.mem_singleton _

end ClusterFamily
end MinorFreeSpanners
