import MinorFreeSpanners.BoundedMinor

/-! Actual minor and finite induced-witness transport through injective
host homomorphisms. Used when a selected regular graph is a real subgraph
of an induced graph, rather than assuming hereditary density or unmatedness. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I V W : Type*} [Fintype V] [Fintype W]
variable {F : SimpleGraph I} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Injective transport of actual branches preserves their width. -/
theorem IsBounded.mapHost (M : MinorModel F G) (f : G →g H)
    (hf : Function.Injective f) {m : ℕ} (hM : M.IsBounded m) :
    (M.mapHost f hf).IsBounded m := by
  classical
  intro i
  have he : ((M.mapHost f hf).branch i).toFinset=
      (M.branch i).toFinset.image f := by
    ext x
    rw [Set.mem_toFinset]
    simp only [Finset.mem_image, Set.mem_toFinset]
    rfl
  rw [he]
  exact (Finset.card_image_le).trans (hM i)

end MinorModel

/-- Injective graph homomorphisms retain distinct actual unordered edges. -/
theorem hom_edge_count_le {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    (hf : Function.Injective f) : G.edgeFinset.card ≤ H.edgeFinset.card := by
  classical
  have hi : Function.Injective (Sym2.map f) := Sym2.map.injective hf
  have hsub : G.edgeFinset.image (Sym2.map f) ⊆ H.edgeFinset := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    induction a using Sym2.inductionOn with
    | hf u v => simpa using f.map_rel (by simpa using ha)
  calc
    _ = (G.edgeFinset.image (Sym2.map f)).card :=
      (Finset.card_image_of_injective _ hi).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The literal image of an induced witness has the same vertex count and
at least as many actual simple edges in the larger host. -/
theorem induced_witness_map {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    (hf : Function.Injective f) (S : Finset V) :
    (S.image f).card=S.card ∧
    (G.induce (S:Set V)).edgeFinset.card ≤
      (H.induce ((S.image f:Finset W):Set W)).edgeFinset.card := by
  classical
  refine ⟨Finset.card_image_of_injective S hf,?_⟩
  let g : (G.induce (S:Set V)) →g (H.induce ((S.image f:Finset W):Set W)) := {
    toFun := fun x => ⟨f x.val,Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩⟩
    map_rel' := fun h => f.map_rel h }
  exact hom_edge_count_le g (fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h)))

end MinorFreeSpanners
