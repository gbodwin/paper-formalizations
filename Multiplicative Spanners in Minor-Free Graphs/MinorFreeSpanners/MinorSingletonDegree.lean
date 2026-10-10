import MinorFreeSpanners.MinorComposition
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace MinorFreeSpanners
open SimpleGraph
namespace MinorModel
variable {I V : Type*} [Fintype I] [Fintype V]
variable {F : SimpleGraph I} {G : SimpleGraph V}
variable [DecidableRel F.Adj] [DecidableRel G.Adj]

/-- A branch consisting of one host vertex cannot represent a target
vertex of larger degree. Its incident target edges inject into the actual
host neighbors by branch-set disjointness. -/
theorem singleton_branch_degree (M : MinorModel F G) (i : I) (a : V)
    (honly : ∀ x ∈ M.branch i, x = a) : F.degree i ≤ G.degree a := by
  classical
  have hex : ∀ j : F.neighborSet i, ∃ y : G.neighborSet a, y.val ∈ M.branch j.val := by
    intro j
    obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent i j.val j.property
    have hxa := honly x hx
    subst x
    exact ⟨⟨y,hxy⟩,hy⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    exact M.branch_unique (hf i) (by simpa only [he] using hf j)
  simpa only [card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hinj

end MinorModel
end MinorFreeSpanners
