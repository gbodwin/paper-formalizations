import MinorFreeSpanners.RootedCompletion
import MinorFreeSpanners.LeafMinor

namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*}
attribute [local instance] Classical.propDecidable

namespace rootedCompletion
variable (G : SimpleGraph V)

/-- An old-vertex walk that avoids the hub stays inside one original component. -/
theorem old_walk_component {u v : V} (p : (rootedCompletion G).Walk (some u) (some v))
    (hnone : none ∉ p.support) : G.connectedComponentMk u = G.connectedComponentMk v := by
  have hS : ∀ x ∈ p.support, x ∈ {x : Option V | x.isSome} := by
    intro x hx
    cases x with
    | none => exact (hnone hx).elim
    | some x => rfl
  let q := p.induce _ hS
  exact ConnectedComponent.eq.mpr ⟨q.map (oldProjection G)⟩

/-- Internal branch walks avoiding the hub stay inside one old component. -/
theorem branch_component {I : Type*} {F : SimpleGraph I}
    (M : MinorModel F (rootedCompletion G)) (i : I) (hi : none ∉ M.branch i)
    {x y : V} (hx : some x ∈ M.branch i) (hy : some y ∈ M.branch i) :
    G.connectedComponentMk x = G.connectedComponentMk y := by
  obtain ⟨p,hp⟩ := M.connected i (some x) hx (some y) hy
  exact old_walk_component G p (fun hn => hi (hp _ hn))

/-- In a clique model, all branches avoiding the hub lie in a single actual
old component. Any branch containing the hub may extend into other components. -/
theorem branches_localize {h : ℕ} (hh : 2 ≤ h)
    (M : MinorModel (⊤ : SimpleGraph (Fin h)) (rootedCompletion G)) :
    ∃ C : G.ConnectedComponent, ∀ i, none ∉ M.branch i →
      ∀ x ∈ M.branch i, ∃ v, x = some v ∧ G.connectedComponentMk v = C := by
  classical
  have hi : ∃ i : Fin h, none ∉ M.branch i := by
    let i : Fin h := ⟨0,by omega⟩
    let j : Fin h := ⟨1,by omega⟩
    by_cases hn : none ∈ M.branch i
    · refine ⟨j,?_⟩
      intro hj
      exact Set.disjoint_left.mp (M.disjoint i j (by intro he; have := congrArg Fin.val he; simp [i,j] at this)) hn hj
    · exact ⟨i,hn⟩
  obtain ⟨i,hi⟩ := hi
  obtain ⟨x,hx⟩ := M.nonempty i
  cases x with
  | none => exact (hi hx).elim
  | some x =>
    refine ⟨G.connectedComponentMk x,?_⟩
    intro j hj y hy
    cases y with
    | none => exact (hj hy).elim
    | some y =>
      refine ⟨y,rfl,?_⟩
      by_cases hij : i = j
      · subst j
        exact (branch_component G M i hi hx hy).symm
      · obtain ⟨a,ha,b,hb,hab⟩ := M.adjacent i j hij
        cases a with
        | none => exact (hi ha).elim
        | some a =>
          cases b with
          | none => exact (hj hb).elim
          | some b =>
            have hab' : G.Adj a b := hab
            exact ((branch_component G M i hi hx ha).trans
              ((ConnectedComponent.eq.mpr hab'.reachable).trans
                (branch_component G M j hj hb hy))).symm

/-- Collapse all other old components to the hub. -/
noncomputable def componentProjection (C : G.ConnectedComponent) : Option V → Option C
  | none => none
  | some v => if hv : v ∈ C.supp then some ⟨v,hv⟩ else none

theorem projection_recovers (C : G.ConnectedComponent) (x : Option V)
    (hx : componentProjection G C x ≠ none) :
    Option.map Subtype.val (componentProjection G C x) = x := by
  cases x with
  | none => exact (hx rfl).elim
  | some x =>
    by_cases hC : x ∈ C.supp
    · simp [componentProjection,hC]
    · simp [componentProjection,hC] at hx

/-- The projection collapses old edges outside the selected component and
maps all other edges into that component with one pendant hub. -/
theorem projection_edges (C : G.ConnectedComponent) {x y : Option V}
    (hxy : (rootedCompletion G).Adj x y) :
    componentProjection G C x = componentProjection G C y ∨
      (leafExtension C.toSimpleGraph ⟨componentRoot G C,componentRoot_mem G C⟩).Adj
        (componentProjection G C x) (componentProjection G C y) := by
  cases x with
  | none =>
    cases y with
    | none => exact hxy.elim
    | some y =>
      by_cases hy : y ∈ C.supp
      · right
        simp only [componentProjection,hy,↓reduceDIte]
        apply Subtype.ext
        exact (show y = componentRoot G (G.connectedComponentMk y) from hxy).trans
          (congrArg (componentRoot G) hy)
      · left; simp [componentProjection,hy]
  | some x =>
    cases y with
    | none =>
      by_cases hx : x ∈ C.supp
      · right
        simp only [componentProjection,hx,↓reduceDIte]
        apply Subtype.ext
        exact (show x = componentRoot G (G.connectedComponentMk x) from hxy).trans
          (congrArg (componentRoot G) hx)
      · left; simp [componentProjection,hx]
    | some y =>
      have hcomp := ConnectedComponent.eq.mpr (show G.Adj x y from hxy).reachable
      by_cases hx : x ∈ C.supp
      · have hy : y ∈ C.supp := hcomp.symm.trans hx
        right
        simp only [componentProjection,hx,hy,↓reduceDIte]
        change G.Adj x y
        exact hxy
      · have hy : y ∉ C.supp := fun hy => hx (hcomp.trans hy)
        left; simp [componentProjection,hx,hy]

variable [Fintype V] [DecidableEq V]

/-- The actual one-hub completion preserves K_h-minor exclusion for h≥3.
No connected-MST convention for disconnected inputs is needed. -/
theorem minorFree {h : ℕ} (hG : CliqueMinorFree G h) (hh : 3 ≤ h) :
    CliqueMinorFree (rootedCompletion G) h := by
  classical
  rintro ⟨M⟩
  obtain ⟨C,hC⟩ := branches_localize G (by omega : 2 ≤ h) M
  let f := componentProjection G C
  have hbad {i : Fin h} {x : Option V} (hx : x ∈ M.branch i) (hf : f x = none) :
      none ∈ M.branch i := by
    by_contra hi
    obtain ⟨v,rfl,hv⟩ := hC i hi x hx
    have hv' : v ∈ C.supp := hv
    simp [f,componentProjection,hv'] at hf
  have hsep : ∀ i j, i ≠ j → ∀ x ∈ M.branch i, ∀ y ∈ M.branch j, f x ≠ f y := by
    intro i j hij x hx y hy he
    have hd := Set.disjoint_left.mp (M.disjoint i j hij)
    by_cases hfx : f x = none
    · exact hd (hbad hx hfx) (hbad hy (he.symm.trans hfx))
    · have hfy : f y ≠ none := fun hy => hfx (he.trans hy)
      have hxy : x = y := (projection_recovers G C x hfx).symm.trans
        ((congrArg (Option.map Subtype.val) he).trans (projection_recovers G C y hfy))
      subst y
      exact hd hx hy
  have hGC : CliqueMinorFree C.toSimpleGraph h := by
    rintro ⟨N⟩
    exact hG ⟨N.mapHost (Embedding.induce C.supp).toHom Subtype.val_injective⟩
  exact leafExtension.minorFree hGC hh ⟨M.mapWeak f (projection_edges G C) hsep⟩

end rootedCompletion
end MinorFreeSpanners
