import MinorFreeSpanners.MinorWeakMap
import MinorFreeSpanners.MinorSingletonDegree

namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*}

/-- Adjoin one pendant vertex, keeping every old edge unchanged. -/
def leafExtension (G : SimpleGraph V) (r : V) : SimpleGraph (Option V) where
  Adj x y := match x,y with
    | none,none => False
    | none,some v => v = r
    | some v,none => v = r
    | some u,some v => G.Adj u v
  symm := ⟨by
    intro x y h
    cases x with
    | none => cases y <;> exact h
    | some x => cases y with
      | none => exact h
      | some y => exact h.symm⟩
  loopless := ⟨by intro x; cases x with
    | none => exact not_false
    | some x => exact G.loopless.irrefl x⟩

namespace leafExtension
variable [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem new_degree_le_one (G : SimpleGraph V) (r : V) : (leafExtension G r).degree none ≤ 1 := by
  classical
  have hs : (leafExtension G r).neighborFinset none ⊆ {some r} := by
    intro x hx
    have ha : (leafExtension G r).Adj none x := by simpa using hx
    cases x with
    | none => exact ha.elim
    | some x => have he : x = r := ha; subst x; simp
  simpa using Finset.card_le_card hs

/-- A clique of order at least three cannot use only the new leaf as a branch. -/
theorem branches_old {G : SimpleGraph V} {r : V} {h : ℕ} (hh : 3 ≤ h)
    (M : MinorModel (⊤ : SimpleGraph (Fin h)) (leafExtension G r)) :
    ∀ i, ∃ x, some x ∈ M.branch i := by
  intro i
  by_contra hn
  push_neg at hn
  have honly : ∀ x ∈ M.branch i, x = none := by
    intro x hx
    cases x with
    | none => rfl
    | some x => exact (hn x hx).elim
  have hd := (M.singleton_branch_degree i none honly).trans (new_degree_le_one G r)
  simp only [complete_graph_degree,Fintype.card_fin] at hd
  omega

/-- A branch containing the new leaf and an old vertex must also contain its root. -/
theorem branch_root {I : Type*} {F : SimpleGraph I} {G : SimpleGraph V} {r : V}
    (M : MinorModel F (leafExtension G r)) (i : I) (hi : none ∈ M.branch i)
    (hold : ∃ x, some x ∈ M.branch i) : some r ∈ M.branch i := by
  obtain ⟨x,hx⟩ := hold
  obtain ⟨p,hp⟩ := M.connected i none hi (some x) hx
  cases p with
  | @cons _ z _ hnz p =>
    cases z with
    | none => exact hnz.elim
    | some z =>
      have hz : some z ∈ M.branch i := hp _ (by simp)
      exact (show z = r from hnz) ▸ hz

/-- Adding a pendant vertex preserves exclusion of every K_h with h≥3. -/
theorem minorFree {G : SimpleGraph V} {r : V} {h : ℕ}
    (hG : CliqueMinorFree G h) (hh : 3 ≤ h) : CliqueMinorFree (leafExtension G r) h := by
  rintro ⟨M⟩
  let f : Option V → V := fun x => x.getD r
  have hf {x y : Option V} (hxy : (leafExtension G r).Adj x y) :
      f x = f y ∨ G.Adj (f x) (f y) := by
    cases x with
    | none =>
      cases y with
      | none => exact hxy.elim
      | some y => exact Or.inl (show y = r from hxy).symm
    | some x =>
      cases y with
      | none => exact Or.inl (show x = r from hxy)
      | some y => exact Or.inr hxy
  have hs : ∀ i j, i ≠ j → ∀ x ∈ M.branch i, ∀ y ∈ M.branch j, f x ≠ f y := by
    intro i j hij x hx y hy he
    have hd := Set.disjoint_left.mp (M.disjoint i j hij)
    have hold := branches_old hh M
    cases x with
    | none =>
      cases y with
      | none => exact hd hx hy
      | some y =>
        have he' : r = y := he
        subst y
        exact hd (branch_root M i hx (hold i)) hy
    | some x =>
      cases y with
      | none =>
        have he' : x = r := he
        subst x
        exact hd hx (branch_root M j hy (hold j))
      | some y =>
        have he' : x = y := he
        subst y
        exact hd hx hy
  exact hG ⟨M.mapWeak f hf hs⟩

end leafExtension
end MinorFreeSpanners
