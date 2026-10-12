import MinorFreeSpanners.OriginalUnpaidEdgeClassification

/-! Every actual block with an unpaid incident heavy edge chooses a retained
old root using that very edge. The chosen host endpoints, adjacency and
unordered original identity are retained for the absorption construction. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

noncomputable def heavyAttachmentBlocks (C : ClusterFamily (I := I) A w D)
    (B : SimpleGraph V) (P : Finset (Finset I)) (paid : Finset I) : Finset (Finset I) := by
  classical
  exact P.filter fun S => (C.unpaidTouchingEdges B S paid).Nonempty

 theorem exists_actual_heavy_attachments (C : ClusterFamily (I := I) A w D)
    (P : Finset (Finset I)) (R paid roots : Finset I)
    (hsub : ∀ S∈P,S⊆R)
    (hcover : ∀ i,i∈R ∨ i∈paid ∨ i∈roots)
    (hno : ∀ i∈R,∀ j∈R,i∉paid → j∉paid →
      ∀ x∈C.branch i,∀ y∈C.branch j,¬B.Adj x y) :
    ∃ owner : {S // S∈C.heavyAttachmentBlocks B P paid} → {r // r∈roots\paid},
    ∃ port : {S // S∈C.heavyAttachmentBlocks B P paid} → I,
    ∃ source target : {S // S∈C.heavyAttachmentBlocks B P paid} → V,
      (∀ S,port S∈S.val\paid ∧ source S∈C.branch (port S) ∧
        target S∈C.branch (owner S).val ∧ B.Adj (source S) (target S) ∧
        s(source S,target S)∈C.unpaidTouchingEdges B S.val paid) ∧
      (∀ S∈P,S∉C.heavyAttachmentBlocks B P paid → C.unpaidTouchingEdges B S paid=∅) := by
  classical
  have hchoose (S : {S // S∈C.heavyAttachmentBlocks B P paid}) :
      ∃ j : {r // r∈roots\paid},∃ i∈S.val\paid,
      ∃ x∈C.branch i,∃ y∈C.branch j.val,B.Adj x y ∧
        s(x,y)∈C.unpaidTouchingEdges B S.val paid := by
    obtain ⟨hSP,e,he⟩ := Finset.mem_filter.mp S.property
    obtain ⟨heS,henot⟩ := Finset.mem_sdiff.mp he
    obtain ⟨hBe,i,hi,j,x,hx,y,hy,heq⟩ := Finset.mem_filter.mp heS
    subst e
    have hxy : B.Adj x y := mem_edgeFinset.mp hBe
    have hip : i∉paid := fun h => henot (C.original_edge_mem_touching paid h hx hy hxy)
    have hjp : j∉paid := by
      intro h
      apply henot
      simpa only [Sym2.eq_swap] using C.original_edge_mem_touching paid h hy hx hxy.symm
    have hjroot : j∈roots := by
      rcases hcover j with hj | hj | hj
      · exact (hno i (hsub S.val hSP hi) j hj hip hjp x hx y hy hxy).elim
      · exact (hjp hj).elim
      · exact hj
    exact ⟨⟨j,Finset.mem_sdiff.mpr ⟨hjroot,hjp⟩⟩,i,Finset.mem_sdiff.mpr ⟨hi,hip⟩,
      x,hx,y,hy,hxy,he⟩
  choose owner port hport source hsource target htarget hedge hmem using hchoose
  refine ⟨owner,port,source,target,fun S => ⟨hport S,hsource S,htarget S,hedge S,hmem S⟩,?_⟩
  intro S hSP hnot
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  exact hnot (Finset.mem_filter.mpr ⟨hSP,e,he⟩)

end ClusterFamily
end MinorFreeSpanners
