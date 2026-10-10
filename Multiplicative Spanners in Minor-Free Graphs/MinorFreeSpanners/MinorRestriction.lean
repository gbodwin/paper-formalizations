import MinorFreeSpanners.MinorComposition
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! Restricting genuine minor models to a component. These lemmas support
copies/padding in the lower-bound construction; they do not assume a
density or minor-exclusion oracle. -/
namespace MinorFreeSpanners
open SimpleGraph
namespace MinorModel
variable {I V W : Type*} {F : SimpleGraph I} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transport branch sets and their actual connecting walks through an
injective graph homomorphism. -/
noncomputable def mapHost (M : MinorModel F G) (f : G →g H)
    (hf : Function.Injective f) : MinorModel F H where
  branch := fun i => f '' M.branch i
  nonempty := fun i => (M.nonempty i).image f
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    have : v = u := hf he
    subst v
    exact Set.disjoint_left.mp (M.disjoint i j hij) hu hv
  connected := by
    rintro i _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
    obtain ⟨p,hp⟩ := M.connected i u hu v hv
    refine ⟨p.map f, ?_⟩
    intro z hz
    rw [Walk.support_map] at hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact ⟨x,hp x hx,rfl⟩
  adjacent := by
    intro i j hij
    obtain ⟨u,hu,v,hv,huv⟩ := M.adjacent i j hij
    exact ⟨f u,⟨u,hu,rfl⟩,f v,⟨v,hv,rfl⟩,f.map_rel huv⟩

/-- A model whose entire branch sets lie in S is a model in the induced
subgraph. The internal walks are restricted explicitly. -/
noncomputable def induce (M : MinorModel F G) (S : Set V)
    (hS : ∀ i, M.branch i ⊆ S) : MinorModel F (G.induce S) where
  branch := fun i => {v | v.val ∈ M.branch i}
  nonempty := by
    intro i
    obtain ⟨v,hv⟩ := M.nonempty i
    exact ⟨⟨v,hS i hv⟩,hv⟩
  disjoint := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun _ hi hj =>
      Set.disjoint_left.mp (M.disjoint i j hij) hi hj)
  connected := by
    intro i u hu v hv
    obtain ⟨p,hp⟩ := M.connected i u.val hu v.val hv
    let q := p.induce S (fun x hx => hS i (hp x hx))
    refine ⟨q, ?_⟩
    intro z hz
    have hz' : z.val ∈ p.support := by
      have hm : z.val ∈ (q.map (Embedding.induce S).toHom).support := by
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨z,hz,rfl⟩
      simpa [q] using hm
    exact hp z.val hz'
  adjacent := by
    intro i j hij
    obtain ⟨u,hu,v,hv,huv⟩ := M.adjacent i j hij
    exact ⟨⟨u,hS i hu⟩,hu,⟨v,hS j hv⟩,hv,huv⟩

/-- Every host vertex in a branch of a connected target is reachable from
any chosen vertex in any other branch. -/
theorem reachable (M : MinorModel F G) (hF : F.Preconnected)
    {i j : I} {u v : V} (hu : u ∈ M.branch i) (hv : v ∈ M.branch j) :
    G.Reachable u v := by
  obtain ⟨p⟩ := hF i j
  obtain ⟨q,_⟩ := M.lift_walk p Set.univ (by simp) hu hv
  exact ⟨q⟩

/-- A minor model of a nonempty connected target is contained in one
actual host connected component. -/
theorem exists_component (M : MinorModel F G) [Nonempty I]
    (hF : F.Preconnected) :
    ∃ C : G.ConnectedComponent, Nonempty (MinorModel F C.toSimpleGraph) := by
  classical
  let i : I := Classical.arbitrary I
  obtain ⟨u,hu⟩ := M.nonempty i
  let C := G.connectedComponentMk u
  refine ⟨C,⟨M.induce C.supp ?_⟩⟩
  intro j v hv
  exact ConnectedComponent.eq.mpr (M.reachable hF hu hv).symm

end MinorModel
end MinorFreeSpanners

namespace MinorFreeSpanners
open SimpleGraph

/-- Clique-minor exclusion can be checked separately on actual connected
components. The positive h boundary is explicit. -/
theorem cliqueMinorFree_of_components {V : Type*} (G : SimpleGraph V)
    (h : ℕ) (hh : 0 < h)
    (hC : ∀ C : G.ConnectedComponent, CliqueMinorFree C.toSimpleGraph h) :
    CliqueMinorFree G h := by
  letI : Nonempty (Fin h) := ⟨⟨0,hh⟩⟩
  rintro ⟨M⟩
  obtain ⟨C,hM⟩ := M.exists_component preconnected_top
  exact hC C hM

attribute [local instance] Classical.propDecidable

/-- This is the exact componentwise edge obstruction used in the source
lower bound. It concerns actual connected components, not an oracle. -/
theorem cliqueMinorFree_of_component_edges {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (h : ℕ) (hh : 0 < h)
    (hC : ∀ C : G.ConnectedComponent,
      C.toSimpleGraph.edgeFinset.card < h.choose 2) :
    CliqueMinorFree G h := by
  classical
  apply cliqueMinorFree_of_components G h hh
  intro C
  exact cliqueMinorFree_of_edges C.toSimpleGraph h (hC C)

end MinorFreeSpanners
