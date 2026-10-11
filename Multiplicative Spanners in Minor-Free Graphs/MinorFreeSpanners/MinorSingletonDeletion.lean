import MinorFreeSpanners.OriginalResidualLoss
import MinorFreeSpanners.BoundedMinor

/-! Deleting specified target branches from the very same minor model.
Every removed quotient edge is charged to an actual host edge incident to
the supplied host set containing those entire branches. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
variable {F : SimpleGraph I} {G : SimpleGraph V}

/-- The filtered edge injection uses the same branch labels as the ordinary
minor edge-count proof, and preserves actual incidence to a deleted branch. -/
theorem incident_edge_count_le (M : MinorModel F G) (D : Finset I) (U : Finset V)
    (hDU : ∀ i∈D, M.branch i ⊆ (U:Set V)) :
    (incidentEdges F D).card ≤ (incidentEdges G U).card := by
  classical
  have hinj : Function.Injective (Sym2.map (some : I → Option I)) :=
    Sym2.map.injective (fun _ _ h => Option.some.inj h)
  have hsub : (incidentEdges F D).image (Sym2.map (some : I → Option I)) ⊆
      (incidentEdges G U).image (Sym2.map M.branchLabel) := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    induction e using Sym2.inductionOn with
    | hf a b =>
      obtain ⟨hab,hd⟩ := (mem_incidentEdges_mk F D a b).mp he
      obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent a b hab
      refine Finset.mem_image.mpr ⟨s(x,y),?_,?_⟩
      · apply (mem_incidentEdges_mk G U x y).mpr
        refine ⟨hxy,?_⟩
        rcases hd with ha | hb
        · exact Or.inl (hDU a ha hx)
        · exact Or.inr (hDU b hb hy)
      · simp only [Sym2.map_mk,M.branchLabel_eq hx,M.branchLabel_eq hy]
  calc
    _ = ((incidentEdges F D).image (Sym2.map (some : I → Option I))).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((incidentEdges G U).image (Sym2.map M.branchLabel)).card := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le

/-- Same-quotient deletion accounting; the retained graph is literally the
induced graph on the undeleted target labels. -/
theorem delete_target_edge_budget (M : MinorModel F G) (D : Finset I) (U : Finset V)
    (hDU : ∀ i∈D, M.branch i ⊆ (U:Set V)) :
    F.edgeFinset.card ≤
      (F.induce ((Finset.univ\D:Finset I):Set I)).edgeFinset.card+(incidentEdges G U).card := by
  rw [edge_count_delete_partition F D]
  exact Nat.add_le_add_left (M.incident_edge_count_le D U hDU) _

end MinorModel

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual quotient labels corresponding to the chosen residual singletons. -/
noncomputable def residualDeletionLabels (C : Finset V) (L : V → Finset V)
    (U : Finset V) (hU : U ⊆ starResidual C L) : Finset (StarContractionVertex C L) :=
  U.attach.image (fun x => Sum.inr (⟨x.val,hU x.property⟩ : starResidual C L))

theorem residualDeletionLabels_card (C : Finset V) (L : V → Finset V)
    (U : Finset V) (hU : U ⊆ starResidual C L) :
    (residualDeletionLabels C L U hU).card=U.card := by
  unfold residualDeletionLabels
  rw [Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro x y he
    have he' : (⟨x.val,hU x.property⟩ : starResidual C L)=⟨y.val,hU y.property⟩ := Sum.inr.inj he
    exact Subtype.ext (congrArg (fun z : starResidual C L => z.val) he')

/-- The retained labels and the removed singleton vertices are counted in
the same canonical quotient of the same actual family. -/
theorem retained_star_quotient_card (G : SimpleGraph V) (k : ℕ) (C : Finset V)
    (L : V → Finset V) (hF : IsGeneralStarForest G k C L) (hk : 1 ≤ k)
    (U : Finset V) (hU : U ⊆ starResidual C L) :
    (Finset.univ\residualDeletionLabels C L U hU).card+U.card+(k-1)*C.card=Fintype.card V := by
  have hq := hF.quotient_card hk
  have hd := residualDeletionLabels_card C L U hU
  have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (residualDeletionLabels C L U hU))
  rw [Finset.card_univ,hd] at hs
  omega

/-- Deleted labels really have their entire singleton branch in U. -/
theorem residualDeletionLabels_branch (G : SimpleGraph V) (k : ℕ) (C : Finset V)
    (L : V → Finset V) (hF : IsGeneralStarForest G k C L)
    (U : Finset V) (hU : U ⊆ starResidual C L) :
    ∀ i∈residualDeletionLabels C L U hU, hF.fullMinorModel.branch i ⊆ (U:Set V) := by
  intro i hi
  obtain ⟨x,_hx,rfl⟩ := Finset.mem_image.mp hi
  intro y hy
  have he : y=x.val := by simpa [IsGeneralStarForest.fullMinorModel,fullStarBranch] using hy
  exact he ▸ x.property

/-- Actual retained bounded minor with an edge-loss budget charged only to
host edges touching the specified deleted residual singletons. -/
theorem retained_star_quotient_budget (G : SimpleGraph V) (k : ℕ) (C : Finset V)
    (L : V → Finset V) (hF : IsGeneralStarForest G k C L) (hk : 1 ≤ k)
    (U : Finset V) (hU : U ⊆ starResidual C L) :
    let R := Finset.univ\residualDeletionLabels C L U hU
    ∃ M : MinorModel ((fullStarContraction G C L).induce (R:Set (StarContractionVertex C L))) G,
      M.IsBounded k ∧
      (fullStarContraction G C L).edgeFinset.card ≤
        ((fullStarContraction G C L).induce (R:Set (StarContractionVertex C L))).edgeFinset.card+
          (incidentEdges G U).card := by
  dsimp only
  refine ⟨hF.fullMinorModel.induceTarget _,MinorModel.IsBounded.induceTarget hF.fullMinorModel (hF.fullMinorModel_bounded hk) _,?_⟩
  exact hF.fullMinorModel.delete_target_edge_budget _ U (residualDeletionLabels_branch G k C L hF U hU)

end MinorFreeSpanners
