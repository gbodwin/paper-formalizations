import MinorFreeSpanners.FullStarContraction

/-! Delete only residual left vertices after contraction, retaining every
right-side vertex as either its selected star or its singleton branch. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def rightStarKeep (B C : Finset V) (L : V → Finset V) :
    Finset (StarContractionVertex C L) := Finset.univ.filter (fun i =>
      match i with | .inl _ => True | .inr x => x.val ∈ B)

/-- The retained real quotient vertices correspond bijectively to the
original right side. Residual left vertices are not counted as centers. -/
theorem IsStarPacking.right_keep_card {G : SimpleGraph V} {A B C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAB : Disjoint A B) (hCB : C ⊆ B) : (rightStarKeep B C L).card=B.card := by
  classical
  let f : StarContractionVertex C L → V := fun i =>
    match i with | .inl b => b.val | .inr x => x.val
  apply Finset.card_bij (fun i _ => f i)
  · intro i hi
    cases i with
    | inl b => exact hCB b.property
    | inr x => simpa [rightStarKeep] using hi
  · intro i hi j hj hij
    cases i with
    | inl b =>
      cases j with
      | inl c => exact congrArg Sum.inl (Subtype.ext hij)
      | inr x =>
        have he : b.val=x.val := hij
        have hn := (Finset.mem_sdiff.mp x.property).2
        exact (hn (Finset.mem_biUnion.mpr ⟨b.val,b.property,by simp [←he]⟩)).elim
    | inr x =>
      cases j with
      | inl b =>
        have he : x.val=b.val := hij
        have hn := (Finset.mem_sdiff.mp x.property).2
        exact (hn (Finset.mem_biUnion.mpr ⟨b.val,b.property,by simp [he]⟩)).elim
      | inr y => exact congrArg Sum.inr (Subtype.ext hij)
  · intro b hb
    by_cases hc : b ∈ C
    · exact ⟨.inl ⟨b,hc⟩,by simp [rightStarKeep],rfl⟩
    · have hr : b ∈ starResidual C L := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        intro hm
        obtain ⟨c,hc',hbc⟩ := Finset.mem_biUnion.mp hm
        rcases Finset.mem_insert.mp hbc with he|hl
        · exact hc (he ▸ hc')
        · exact Finset.disjoint_left.mp hAB (h.2.1 c hl) hb
      exact ⟨.inr ⟨b,hr⟩,by simp [rightStarKeep,hb],rfl⟩

/-- Literal induced subgraph of the full simple contraction, retaining all
right-side labels and no residual left-side labels. -/
noncomputable def rightStarQuotient (G : SimpleGraph V) (B C : Finset V)
    (L : V → Finset V) : SimpleGraph (rightStarKeep B C L) :=
  (fullStarContraction G C L).induce (rightStarKeep B C L:Set (StarContractionVertex C L))

/-- Restriction of the actual covering model constructs the right-retained
minor; its branches are still the same literal stars or singletons. -/
noncomputable def IsStarPacking.rightMinorModel {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) (hAC : Disjoint A C) :
    MinorModel (rightStarQuotient G B C L) G where
  branch i := (h.fullMinorModel hAC).branch i.val
  nonempty i := (h.fullMinorModel hAC).nonempty i.val
  disjoint i j hij := (h.fullMinorModel hAC).disjoint i.val j.val
    (fun he => hij (Subtype.ext he))
  connected i := (h.fullMinorModel hAC).connected i.val
  adjacent i j he := (h.fullMinorModel hAC).adjacent i.val j.val he

/-- Removing residual left labels does not increase branch width. -/
theorem IsStarPacking.rightMinorModel_bounded {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) (hAC : Disjoint A C) :
    (h.rightMinorModel (B:=B) hAC).IsBounded (ell+1) := by
  intro i
  exact h.fullMinorModel_bounded hAC i.val

/-- Every discarded quotient label is exactly an uncovered original left
vertex, when the original finite sides cover the host. -/
theorem right_deleted_card {A B C : Finset V} {L : V → Finset V}
    (hAB : Disjoint A B) (hCB : C ⊆ B) (hcover : A ∪ B=Finset.univ) :
    (Finset.univ \ rightStarKeep B C L).card=(A \ C.biUnion L).card := by
  classical
  let f : StarContractionVertex C L → V := fun i =>
    match i with | .inl b => b.val | .inr x => x.val
  have hnotB : ∀ x : starResidual C L,
      Sum.inr x ∈ Finset.univ \ rightStarKeep B C L ↔ x.val ∉ B := by
    intro x
    simp [rightStarKeep]
  apply Finset.card_bij (fun i _ => f i)
  · intro i hi
    cases i with
    | inl b => simp [rightStarKeep] at hi
    | inr x =>
      have hn := (hnotB x).mp hi
      have hxA : x.val ∈ A := by
        have hm : x.val ∈ A ∪ B := hcover.symm ▸ Finset.mem_univ _
        exact (Finset.mem_union.mp hm).resolve_right hn
      refine Finset.mem_sdiff.mpr ⟨hxA,?_⟩
      intro hl
      obtain ⟨b,hb,hl⟩ := Finset.mem_biUnion.mp hl
      exact (Finset.mem_sdiff.mp x.property).2
        (Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_insert_of_mem hl⟩)
  · intro i hi j hj hij
    cases i with
    | inl b => simp [rightStarKeep] at hi
    | inr x =>
      cases j with
      | inl b => simp [rightStarKeep] at hj
      | inr y => exact congrArg Sum.inr (Subtype.ext hij)
  · intro x hx
    obtain ⟨hxA,hxL⟩ := Finset.mem_sdiff.mp hx
    have hxB : x ∉ B := fun hb => Finset.disjoint_left.mp hAB hxA hb
    have hr : x ∈ starResidual C L := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro hm
      obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hm
      rcases Finset.mem_insert.mp hx with he|hl
      · exact hxB (he ▸ hCB hb)
      · exact hxL (Finset.mem_biUnion.mpr ⟨b,hb,hl⟩)
    exact ⟨.inr ⟨x,hr⟩,(hnotB _).mpr hxB,rfl⟩

end MinorFreeSpanners
