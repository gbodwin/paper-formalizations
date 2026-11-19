import OnlineReachabilityPreservers.LocalInducedPaths

/-! The source-restricted incidence bound with each path's own order. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I]

local notation "ListBefore" => SourceAudit.BeforeIn

omit [LinearOrder I] in
/-- The order on two retained vertices agrees with their original order. -/
theorem listBefore_sublist_iff {paths cut : I → List V} {i : I} {u v : V}
    (simple : (paths i).Nodup) (sub : List.Sublist (cut i) (paths i))
    (hu : u ∈ cut i) (hv : v ∈ cut i) : ListBefore cut i u v ↔ ListBefore paths i u v := by
  refine ⟨listBefore_of_sublist simple sub, ?_⟩
  intro old
  rcases listBefore_total hu hv (listBefore_ne old) with forward | backward
  · exact forward
  · have reverse := listBefore_of_sublist simple sub backward
    exact False.elim (lt_asymm old.2.2 reverse.2.2)

private theorem list_source_collision {paths : I → List V} {source : I → V}
    (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (starts : ∀ i v, v ∈ (paths i).toFinset.erase (source i) → ListBefore paths i (source i) v)
    {i j k : I} (ij : i < j) (ik : i < k) {x y : V}
    (xi : x ∈ (paths i).toFinset.erase (source i)) (xj : x ∈ (paths j).toFinset.erase (source j))
    (yi : y ∈ (paths i).toFinset.erase (source i)) (yk : y ∈ (paths k).toFinset.erase (source k))
    (equalSource : source j = source k) : x = y ∧ j = k := by
  have forbid {j k : I} {x y : V} (ij : i < j) (ik : i < k) (step : ListBefore paths i x y)
      (first : ListBefore paths j (source j) x) (last : ListBefore paths k (source k) y)
      (equalSource : source j = source k) : False := by
    by_cases same : j = k
    · subst k
      exact (listBefore_ne step) (unique ij.ne step.1 first.2.1 step.2.1 last.2.1)
    exact free (by decide) (threeListBridge ij.ne' (fun eq => same eq.symm) ik.ne'
      first step (equalSource.symm ▸ last)) ik
  have xOn := List.mem_toFinset.mp (mem_erase.mp xi).2
  have yOn := List.mem_toFinset.mp (mem_erase.mp yi).2
  have xStep := starts _ _ xj
  have yStep := starts _ _ yk
  by_cases equal : x = y
  · subst y
    refine ⟨rfl, ?_⟩
    by_contra different
    have together := unique (show j ≠ k from different) xStep.1 (equalSource.symm ▸ yStep.1)
      xStep.2.1 yStep.2.1
    exact (listBefore_ne xStep) together
  rcases listBefore_total xOn yOn equal with early | late
  · exact (forbid ij ik early xStep yStep equalSource).elim
  · exact (forbid ik ij late yStep xStep equalSource.symm).elim

variable [Fintype V] [Fintype I]

/-- The source-restricted square bound in a local path order. The charged
incidences exclude the chosen first vertex. -/
theorem list_source_restricted_square {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (S : Finset V) (source : I → V) (inside : ∀ i, source i ∈ S)
    (starts : ∀ i v, v ∈ (paths i).toFinset.erase (source i) → ListBefore paths i (source i) v) :
    let m := ∑ i, ((paths i).toFinset.erase (source i)).card
    m^2 ≤ Fintype.card V*(m+2*(Fintype.card I*S.card)) := by
  let marks (i : I) := (paths i).toFinset.erase (source i)
  let charge (z : V × I × I) := (z.2.1, source z.2.2)
  have bound : (collisions marks).card ≤ Fintype.card I*S.card := calc
    _ ≤ ((univ : Finset I) ×ˢ S).card := by
      apply card_le_card_of_injOn charge
      · rintro ⟨x, i, j⟩ _
        exact mem_product.mpr ⟨mem_univ _, inside j⟩
      · rintro ⟨x, i, j⟩ one ⟨y, i', k⟩ two eq
        change (i, source j) = (i', source k) at eq
        obtain ⟨rfl, same⟩ := Prod.mk.inj eq
        obtain ⟨_, ij, xi, xj⟩ := mem_filter.mp one
        obtain ⟨_, ik, yi, yk⟩ := mem_filter.mp two
        obtain ⟨rfl, rfl⟩ := list_source_collision free unique starts ij ik xi xj yi yk same
        rfl
    _ = _ := by simp
  exact incidence_square marks _ bound

end OnlineReachabilityPreservers
