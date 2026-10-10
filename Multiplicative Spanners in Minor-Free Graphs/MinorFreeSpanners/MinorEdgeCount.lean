import MinorFreeSpanners.Minor
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! A minor cannot have more edges than its host. This is proved directly
from disjoint branch sets, and supplies the clique-minor exclusion used in
the lower-bound construction. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
namespace MinorModel
variable {I V : Type*} {F : SimpleGraph I} {G : SimpleGraph V}

theorem branch_unique (M : MinorModel F G) {i j : I} {v : V}
    (hi : v ∈ M.branch i) (hj : v ∈ M.branch j) : i = j := by
  by_contra h
  exact Set.disjoint_left.mp (M.disjoint i j h) hi hj

noncomputable def branchLabel (M : MinorModel F G) (v : V) : Option I := by
  classical
  exact if h : ∃ i, v ∈ M.branch i then some h.choose else none

theorem branchLabel_eq (M : MinorModel F G) {i : I} {v : V}
    (hv : v ∈ M.branch i) : M.branchLabel v = some i := by
  classical
  unfold branchLabel
  split_ifs with h
  · exact congrArg some (M.branch_unique h.choose_spec hv)
  · exact (h ⟨i,hv⟩).elim

variable [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
variable [DecidableRel F.Adj] [DecidableRel G.Adj]

theorem edge_count_le (M : MinorModel F G) : F.edgeFinset.card ≤ G.edgeFinset.card := by
  classical
  have hinj : Function.Injective (Sym2.map (some : I → Option I)) :=
    Sym2.map.injective (fun _ _ h => Option.some.inj h)
  have hsub : F.edgeFinset.image (Sym2.map (some : I → Option I)) ⊆
      G.edgeFinset.image (Sym2.map M.branchLabel) := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := mem_image.mp hz
    induction e using Sym2.inductionOn with
    | hf a b =>
      obtain ⟨u, hu, v, hv, huv⟩ := M.adjacent a b (by simpa using he)
      refine mem_image.mpr ⟨s(u,v), by simpa using huv, ?_⟩
      simp only [Sym2.map_mk, M.branchLabel_eq hu, M.branchLabel_eq hv]
  calc
    F.edgeFinset.card = (F.edgeFinset.image (Sym2.map (some : I → Option I))).card :=
      (card_image_of_injective _ hinj).symm
    _ ≤ (G.edgeFinset.image (Sym2.map M.branchLabel)).card := card_le_card hsub
    _ ≤ G.edgeFinset.card := card_image_le
end MinorModel

variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A graph with fewer than binomial(h,2) edges has no Kₕ minor. -/
theorem cliqueMinorFree_of_edges (G : SimpleGraph V) (h : ℕ)
    (hm : G.edgeFinset.card < h.choose 2) : CliqueMinorFree G h := by
  rintro ⟨M⟩
  have hb := M.edge_count_le
  have hc : (⊤ : SimpleGraph (Fin h)).edgeFinset.card = h.choose 2 := by
    simpa only [Fintype.card_fin] using
      (card_edgeFinset_top_eq_card_choose_two (V := Fin h))
  rw [hc] at hb
  exact (not_le_of_gt hm) hb

end MinorFreeSpanners
