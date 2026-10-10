import MinorFreeSpanners.Minor
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Extend an actual complete minor model by a connected residual branch. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {G : SimpleGraph V}

noncomputable def extendCliqueModel
    (M : MinorModel (⊤ : SimpleGraph (Fin r)) G) (S C : Finset V)
    (hinside : ∀ i, M.branch i ⊆ (S:Set V))
    (hdom : ∀ i x, x ∉ S → ∃ y ∈ M.branch i, G.Adj y x)
    (hne : C.Nonempty) (hdisj : Disjoint C S)
    (hconn : ∀ x ∈ C, ∀ y ∈ C, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ C) :
    MinorModel (⊤ : SimpleGraph (Fin (r+1))) G where
  branch := Fin.cons (C:Set V) M.branch
  nonempty := by
    intro i
    induction i using Fin.cases with
    | zero => exact hne
    | succ i => exact M.nonempty i
  disjoint := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        apply Set.disjoint_left.mpr
        intro x hx hxj
        exact Finset.disjoint_left.mp hdisj hx (hinside j hxj)
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        apply Set.disjoint_left.mpr
        intro x hxi hx
        exact Finset.disjoint_left.mp hdisj hx (hinside i hxi)
      | succ j => exact M.disjoint i j (fun h => hij (congrArg Fin.succ h))
  connected := by
    intro i
    induction i using Fin.cases with
    | zero => exact hconn
    | succ i => exact M.connected i
  adjacent := by
    intro i j hij
    have hneq : i ≠ j := by simpa using hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hneq rfl).elim
      | succ j =>
        obtain ⟨x,hx⟩ := hne
        have hxS : x ∉ S := fun h => Finset.disjoint_left.mp hdisj hx h
        obtain ⟨y,hy,hyx⟩ := hdom j x hxS
        exact ⟨x,hx,y,hy,hyx.symm⟩
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        obtain ⟨x,hx⟩ := hne
        have hxS : x ∉ S := fun h => Finset.disjoint_left.mp hdisj hx h
        obtain ⟨y,hy,hyx⟩ := hdom i x hxS
        exact ⟨y,hy,x,hx,hyx⟩
      | succ j =>
        apply M.adjacent i j
        simpa using hneq

end MinorFreeSpanners
