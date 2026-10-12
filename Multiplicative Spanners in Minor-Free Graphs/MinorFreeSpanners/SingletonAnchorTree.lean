import MinorFreeSpanners.SelectedResidualClusters
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Selecting one original label as an artificial root changes only its name.
The mixed index type is explicitly equivalent to the original labels, so the
entire original tree and every residual adjacency are retained literally. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

noncomputable def singletonAnchorEquiv {I : Type*} (anchor : I) :
    SelectedResidualIndex ({{anchor}} : Finset (Finset I)) ≃ I := by
  classical
  let f : SelectedResidualIndex ({{anchor}} : Finset (Finset I)) → I :=
    Sum.elim (fun _ => anchor) Subtype.val
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        exact congrArg Sum.inl (Subtype.ext ((Finset.mem_singleton.mp a.property).trans
          (Finset.mem_singleton.mp b.property).symm))
      | inr b =>
        change anchor=b.val at hab
        exact False.elim (b.property (by simp [←hab]))
    | inr a =>
      cases b with
      | inl b =>
        change a.val=anchor at hab
        exact False.elim (a.property (by simp [hab]))
      | inr b =>
        exact congrArg Sum.inr (Subtype.ext hab)
  · intro i
    by_cases hi : i=anchor
    · subst i
      exact ⟨Sum.inl ⟨{anchor},by simp⟩,rfl⟩
    · exact ⟨Sum.inr ⟨i,by simpa using hi⟩,rfl⟩

noncomputable def singletonAnchorFamily {I V : Type*} {A G : SimpleGraph V}
    {w : Sym2 V → ℝ} {D E : ℝ} (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (anchor : I) (hDE : D≤E) :
    ClusterFamily (I:={S : Finset I // S∈({{anchor}} : Finset (Finset I))}) G w E where
  branch := fun _ => C.branch anchor
  nonempty := fun _ => C.nonempty anchor
  disjoint := by
    intro a b hab
    exact False.elim (hab (Subtype.ext ((Finset.mem_singleton.mp a.property).trans
      (Finset.mem_singleton.mp b.property).symm)))
  connected := by
    intro _ x hx y hy
    obtain ⟨p,hp,hw⟩ := C.connected anchor x hx y hy
    exact ⟨p.mapLe hA,by simpa using hp,by simpa using hw.trans hDE⟩

 theorem singletonAnchorFamily_branch {I V : Type*} {A G : SimpleGraph V}
    {w : Sym2 V → ℝ} {D E : ℝ} (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (anchor : I) (hDE : D≤E)
    (S : {S : Finset I // S∈({{anchor}} : Finset (Finset I))}) :
    (singletonAnchorFamily C hA anchor hDE).branch S={x | ∃ i∈S.val,x∈C.branch i} := by
  have hS : S.val={anchor} := Finset.mem_singleton.mp S.property
  ext x
  simp [singletonAnchorFamily,hS]

noncomputable def singletonAnchorTree {I : Type*} (H : SimpleGraph I) (anchor : I) :
    SimpleGraph (SelectedResidualIndex ({{anchor}} : Finset (Finset I))) :=
  H.comap (singletonAnchorEquiv anchor)

 theorem singletonAnchorTree_isTree {I : Type*} (H : SimpleGraph I) (anchor : I)
    (hH : H.IsTree) : (singletonAnchorTree H anchor).IsTree :=
  (SimpleGraph.Iso.comap (singletonAnchorEquiv anchor) H).isTree_iff.mpr hH

 theorem singletonAnchorTree_residual_adj {I : Type*} (H : SimpleGraph I) (anchor : I)
    (i j : {i : I // i∉({{anchor}} : Finset (Finset I)).biUnion id}) :
    (singletonAnchorTree H anchor).Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val :=
  Iff.rfl

end MinorFreeSpanners
