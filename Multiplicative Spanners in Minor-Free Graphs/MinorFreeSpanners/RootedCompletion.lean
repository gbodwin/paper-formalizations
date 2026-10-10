import MinorFreeSpanners.GirthComponents
import Mathlib.Logic.Equiv.Option

/-! A genuine connected augmentation, used to avoid assigning an MST ratio
  to the disconnected sparse lower-bound construction. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*}

noncomputable def componentRoot (G : SimpleGraph V) (C : G.ConnectedComponent) : V :=
  C.exists_rep.choose

@[simp] theorem componentRoot_mem (G : SimpleGraph V) (C : G.ConnectedComponent) :
    G.connectedComponentMk (componentRoot G C) = C := C.exists_rep.choose_spec

/-- Add one new hub and exactly one edge to a chosen vertex of each actual
connected component. No connected-core assumption is supplied. -/
noncomputable def rootedCompletion (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj x y := match x,y with
    | none,none => False
    | none,some v => v = componentRoot G (G.connectedComponentMk v)
    | some v,none => v = componentRoot G (G.connectedComponentMk v)
    | some u,some v => G.Adj u v
  symm := ⟨by
    intro x y h
    cases x with
    | none => cases y <;> exact h
    | some x =>
      cases y with
      | none => exact h
      | some y => exact h.symm⟩
  loopless := ⟨by intro x; cases x with
    | none => exact not_false
    | some x => exact G.loopless.irrefl x⟩

namespace rootedCompletion
variable (G : SimpleGraph V)

/-- The old graph embeds literally into its connected completion. -/
def oldEmbedding : G →g rootedCompletion G where
  toFun := some
  map_rel' := fun h => h

theorem connected : (rootedCompletion G).Connected := by
  have hr : ∀ x, (rootedCompletion G).Reachable x none := by
    intro x
    cases x with
    | none => exact Reachable.refl _
    | some v =>
      have he : G.connectedComponentMk v = G.connectedComponentMk
          (componentRoot G (G.connectedComponentMk v)) := (componentRoot_mem _ _).symm
      obtain ⟨p⟩ := ConnectedComponent.eq.mp he
      have hlast : (rootedCompletion G).Adj
          (some (componentRoot G (G.connectedComponentMk v))) none := by
        change componentRoot G (G.connectedComponentMk v) = _
        rw [componentRoot_mem]
      exact ⟨(p.map (oldEmbedding G)).concat hlast⟩
  exact ⟨fun x y => (hr x).trans (hr y).symm⟩

/-- Every newly added hub edge is an actual graph bridge. -/
theorem new_edge_bridge (C : G.ConnectedComponent) :
    (rootedCompletion G).IsBridge s(none,some (componentRoot G C)) := by
  let D := (rootedCompletion G).deleteEdges {s(none,some (componentRoot G C))}
  let marked : Option V → Prop := fun x => match x with
    | none => False
    | some v => G.connectedComponentMk v = C
  have hstep {x y : Option V} (hxy : D.Adj x y) (hx : marked x) : marked y := by
    cases x with
    | none => exact hx.elim
    | some x =>
      cases y with
      | none =>
        have hxC : G.connectedComponentMk x = C := hx
        have hxrep : x = componentRoot G (G.connectedComponentMk x) := hxy.1
        rw [hxC] at hxrep
        exact (hxy.2 (by simp [hxrep,Sym2.eq_swap])).elim
      | some y =>
        have hcomp := ConnectedComponent.eq.mpr (show G.Adj x y from hxy.1).reachable
        exact hcomp.symm.trans hx
  have hwalk {x y : Option V} (p : D.Walk x y) : marked x → marked y := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hx => ih (hstep h hx)
  change ¬ D.Reachable none (some (componentRoot G C))
  rintro ⟨p⟩
  exact hwalk p.reverse (componentRoot_mem G C)

/-- No actual cycle contains the hub as its base vertex. -/
theorem not_cycle_at_hub (p : (rootedCompletion G).Walk none none) : ¬ p.IsCycle := by
  intro hp
  cases p with
  | nil => exact Walk.not_isCycle_nil hp
  | @cons _ x _ hx p =>
    cases x with
    | none => exact hx.elim
    | some x =>
      have hrep : x = componentRoot G (G.connectedComponentMk x) := hx
      exact (new_edge_bridge G (G.connectedComponentMk x)).notMem_edges_of_isCycle hp
        (by simp [← hrep])

/-- Projection from the induced old-vertex graph is an actual isomorphism
on vertices and a graph homomorphism. -/
def oldProjection : ((rootedCompletion G).induce {x | x.isSome}) →g G where
  toFun := Equiv.optionIsSomeEquiv V
  map_rel' := by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy
    cases x with
    | none => simp at hx
    | some x =>
      cases y with
      | none => simp at hy
      | some y => exact hxy

/-- Adding the connecting bridges creates no new cycles, hence preserves
all finite unweighted girth lower bounds. -/
theorem girth {r : ℕ} (hg : GirthAbove G r) : GirthAbove (rootedCompletion G) r := by
  classical
  intro a p hp
  have hS : ∀ x ∈ p.support, x ∈ {x : Option V | x.isSome} := by
    intro x hx
    cases x with
    | none => exact (not_cycle_at_hub G (p.rotate none hx) (hp.rotate hx)).elim
    | some x => rfl
  let q := p.induce _ hS
  have hq : q.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce _).toHom)
    simpa [q] using hp
  have hlen := hg _ (q.map (oldProjection G))
    (hq.map (Equiv.optionIsSomeEquiv V).injective)
  have he : q.length = p.length := by
    have hm : (q.map (Embedding.induce _).toHom).length = q.length := Walk.length_map _ _
    exact hm.symm.trans (congrArg (fun w : (rootedCompletion G).Walk a a => w.length)
      (p.map_induce hS))
  simpa only [Walk.length_map,he] using hlen

end rootedCompletion
end MinorFreeSpanners
