import MinorFreeSpanners.MinorSingletonDegree
import MinorFreeSpanners.LowerBound
import Mathlib.Combinatorics.SimpleGraph.Star

namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*}

/-- A walk in a star avoiding its center has identical endpoints. -/
theorem star_walk_avoiding_center (r : V) {u v : V}
    (p : (starGraph r).Walk u v) (hr : r ∉ p.support) : u = v := by
  cases p with
  | nil => rfl
  | cons h p =>
    rcases (starGraph_adj.mp h).2 with rfl | rfl
    · exact (hr (by simp)).elim
    · exact (hr (by simp)).elim

variable [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A real star excludes every clique minor of order at least three. -/
theorem star_minorFree (r : V) (h : ℕ) (hh : 3 ≤ h) : CliqueMinorFree (starGraph r) h := by
  classical
  rintro ⟨M⟩
  have hcenter (i : Fin h) : r ∈ M.branch i := by
    by_contra hi
    obtain ⟨a,ha⟩ := M.nonempty i
    have har : a ≠ r := fun he => hi (he ▸ ha)
    have honly : ∀ x ∈ M.branch i, x = a := by
      intro x hx
      obtain ⟨p,hp⟩ := M.connected i x hx a ha
      exact star_walk_avoiding_center r p (fun h => hi (hp r h))
    have hd := M.singleton_branch_degree i a honly
    rw [degree_starGraph_of_ne_center har] at hd
    have hd' : h-1 ≤ 1 := by simpa using hd
    omega
  let i : Fin h := ⟨0,by omega⟩
  let j : Fin h := ⟨1,by omega⟩
  exact Set.disjoint_left.mp (M.disjoint i j (by intro he; have := congrArg Fin.val he; simp [i,j] at this))
    (hcenter i) (hcenter j)

theorem star_girth (r : V) (k : ℕ) : GirthAbove (starGraph r) k := by
  intro a p hp
  exact (isAcyclic_starGraph r p hp).elim

/-- Every multiplicative spanner of a unit-weight star retains its n−1 edges. -/
theorem star_spanner_edges (r : V) (k : ℕ) (H : SimpleGraph V)
    (hH : LightSpanners.IsSpanner (starGraph r) H (fun _ => 1) (2*k-1)) :
    H.edgeFinset.card+1 = Fintype.card V := by
  have he := high_girth_spanner_eq k (star_girth r (2*k)) hH
  subst H
  convert (isTree_starGraph r).card_edgeFinset using 1
  congr 2
  ext e
  simp only [mem_edgeFinset]

end MinorFreeSpanners
