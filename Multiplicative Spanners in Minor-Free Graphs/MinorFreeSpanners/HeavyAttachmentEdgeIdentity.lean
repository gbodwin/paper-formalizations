import MinorFreeSpanners.ResidualHeavyAttachment

/-! Distinct actual residual blocks use distinct original attachment edges.
The proof rules out an orientation swap by residual core exclusion, and
uses actual disjoint host branches rather than a simple quotient count. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem heavy_attachment_edges_injective (C : ClusterFamily (I := I) A w D)
    (P : Finset (Finset I)) (R paid roots : Finset I)
    (hsub : ∀ S∈P,S⊆R)
    (hdis : ∀ S∈P,∀ T∈P,S≠T → Disjoint S T)
    (hno : ∀ i∈R,∀ j∈R,i∉paid → j∉paid →
      ∀ x∈C.branch i,∀ y∈C.branch j,¬B.Adj x y)
    (owner : {S // S∈C.heavyAttachmentBlocks B P paid} → {r // r∈roots\paid})
    (port : {S // S∈C.heavyAttachmentBlocks B P paid} → I)
    (source target : {S // S∈C.heavyAttachmentBlocks B P paid} → V)
    (hport : ∀ S,port S∈S.val\paid)
    (hs : ∀ S,source S∈C.branch (port S))
    (ht : ∀ S,target S∈C.branch (owner S).val)
    (hedge : ∀ S,B.Adj (source S) (target S)) :
    Function.Injective (fun S => s(source S,target S)) := by
  classical
  have hmem (S : {S // S∈C.heavyAttachmentBlocks B P paid}) : S.val∈P :=
    (Finset.mem_filter.mp S.property).1
  have hpr (S : {S // S∈C.heavyAttachmentBlocks B P paid}) : port S∈R :=
    hsub S.val (hmem S) (Finset.mem_sdiff.mp (hport S)).1
  have hroot (S : {S // S∈C.heavyAttachmentBlocks B P paid}) : (owner S).val∉R := by
    intro hr
    exact hno (port S) (hpr S) (owner S).val hr (Finset.mem_sdiff.mp (hport S)).2
      (Finset.mem_sdiff.mp (owner S).property).2 (source S) (hs S) (target S) (ht S) (hedge S)
  have label_eq {i j : I} {x : V} (hx : x∈C.branch i) (hy : x∈C.branch j) : i=j := by
    by_contra hne
    exact Set.disjoint_left.mp (C.disjoint i j hne) hx hy
  intro S T he
  rcases Sym2.eq_iff.mp he with he | he
  · have hp : port S=port T := label_eq (hs S) (he.1.symm ▸ hs T)
    apply Subtype.ext
    by_contra hne
    exact Finset.disjoint_left.mp (hdis S.val (hmem S) T.val (hmem T) hne)
      (Finset.mem_sdiff.mp (hport S)).1 (hp.symm ▸ (Finset.mem_sdiff.mp (hport T)).1)
  · have hp : port S=(owner T).val := label_eq (hs S) (he.1.symm ▸ ht T)
    exact (hroot T (hp ▸ hpr S)).elim

end ClusterFamily
end MinorFreeSpanners
