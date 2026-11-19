import OnlineReachabilityPreservers.LocalOrderExtremal

/-! The exact gain from nonempty paths, with a sharp example. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Two paths traversing the same vertices in opposite orders. -/
def oppositeRows (n : ℕ) (i : Fin 2) : List (Fin n) :=
  if i = 0 then List.finRange n else List.ofFn (Fin.rev : Fin n → Fin n)

private theorem oppositeRows_simple (n : ℕ) (i : Fin 2) : (oppositeRows n i).Nodup := by
  by_cases first : i = 0
  · simpa only [oppositeRows,first,↓reduceIte] using List.nodup_finRange n
  · simpa only [oppositeRows,first,↓reduceIte] using List.nodup_ofFn_ofInjective (Fin.rev_injective (n := n))

private theorem oppositeRows_mem {n : ℕ} (i : Fin 2) (v : Fin n) : v ∈ oppositeRows n i := by
  by_cases first : i = 0
  · simp [oppositeRows,first]
  · simp only [oppositeRows,first,↓reduceIte,List.mem_ofFn]
    exact ⟨v.rev,Fin.rev_rev _⟩

private theorem oppositeRows_ascending {n : ℕ} {x y : Fin n} :
    ListBefore (oppositeRows n) 0 x y ↔ x.val < y.val := by
  unfold SourceAudit.BeforeIn
  simp only [oppositeRows, ↓reduceIte, List.mem_finRange, true_and, List.idxOf_finRange]

private theorem oppositeRows_descending {n : ℕ} {x y : Fin n} :
    ListBefore (oppositeRows n) 1 x y ↔ y.val < x.val := by
  have idx (v : Fin n) : (oppositeRows n 1).idxOf v = v.rev.val := by
    have nodup := oppositeRows_simple n 1
    have bound : v.rev.val < (oppositeRows n 1).length := by
      simpa [oppositeRows] using v.rev.isLt
    have nth := nodup.idxOf_getElem v.rev.val bound
    have value : (oppositeRows n 1)[v.rev.val] = v := by
      simp only [oppositeRows, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, List.getElem_ofFn]
      exact Fin.rev_rev v
    rwa [value] at nth
  unfold SourceAudit.BeforeIn
  simp only [oppositeRows_mem, true_and, idx, Fin.val_rev]
  omega

theorem oppositeRows_bridge_free (n k : ℕ) :
    BridgeFree (ListBefore (oppositeRows n)) k := by
  intro s _
  refine ⟨fun b => ?_⟩
  cases s with
  | zero =>
    have paths := b.river_ne_arc 0
    have river := b.riverStep
    have arc := b.arcStep 0
    change ListBefore (oppositeRows n) (b.arc 0) (b.vertex 0) (b.vertex (Fin.last 1)) at arc
    have cases (i : Fin 2) : i = 0 ∨ i = 1 := by
      fin_cases i <;> simp
    rcases cases b.river with hr | hr <;> rcases cases (b.arc 0) with ha | ha <;>
      rw [hr,ha] at paths <;> rw [hr] at river <;> rw [ha] at arc
    · exact paths rfl
    · exact Nat.lt_asymm (oppositeRows_ascending.mp river) (oppositeRows_descending.mp arc)
    · exact Nat.lt_asymm (oppositeRows_ascending.mp arc) (oppositeRows_descending.mp river)
    · exact paths rfl
  | succ s =>
    have p : (b.river).val ≠ (b.arc 0).val := fun h => b.river_ne_arc 0 (Fin.ext h)
    have q : (b.river).val ≠ (b.arc 1).val := fun h => b.river_ne_arc 1 (Fin.ext h)
    have r : (b.arc 0).val ≠ (b.arc 1).val := by
      intro h
      have eq := b.distinctArcs (Fin.ext h)
      have value := congrArg Fin.val eq
      change 0 = 1 at value
      omega
    have p₂ := (b.river).isLt
    have q₂ := (b.arc 0).isLt
    have r₂ := (b.arc 1).isLt
    omega

private theorem firstOppositeRow_kept (n : ℕ) :
    removeOppositeIntersections (oppositeRows n) 0 = oppositeRows n 0 := by
  have earlierEmpty : IsEmpty {j : Fin 2 // j < 0} :=
    ⟨fun j => not_lt_zero j.property⟩
  let _ := earlierEmpty
  rw [removeOppositeIntersections]
  apply List.filter_eq_self.mpr
  intro x _
  simp

private theorem secondOppositeRow_members {n : ℕ} (hn : 0 < n) (v : Fin n) :
    v ∈ removeOppositeIntersections (oppositeRows n) 1 ↔ v = ⟨0,hn⟩ := by
  let zero : Fin n := ⟨0,hn⟩
  rw [removeOppositeIntersections_mem]
  refine ⟨fun kept => ?_,?_⟩
  · by_contra ne
    have pos : 0 < v.val := Nat.pos_of_ne_zero (fun h => ne (Fin.ext h))
    have retained : ListBefore (removeOppositeIntersections (oppositeRows n)) 0 zero v := by
      unfold SourceAudit.BeforeIn
      rw [firstOppositeRow_kept]
      exact oppositeRows_ascending.mpr pos
    exact kept.2 ⟨0,by decide,zero,oppositeRows_descending.mpr pos,retained⟩
  · rintro rfl
    refine ⟨oppositeRows_mem _ _,?_⟩
    rintro ⟨j,_,u,step,_⟩
    have impossible : u.val < 0 := oppositeRows_descending.mp step
    omega

/-- Two opposite rows attain equality in the pruning bound for every
positive vertex count. -/
theorem oppositeRows_pruning_sharp {n : ℕ} (hn : 0 < n) :
    (∑ i, (oppositeRows n i).length) = 2*n ∧
      (∑ i, (removeOppositeIntersections (oppositeRows n) i).length) = n+1 := by
  have nodup := (removeOppositeIntersections_sublist (oppositeRows n) 1).nodup (oppositeRows_simple n 1)
  have set : (removeOppositeIntersections (oppositeRows n) 1).toFinset = {⟨0,hn⟩} := by
    ext v
    simp only [List.mem_toFinset,mem_singleton,secondOppositeRow_members hn]
  have one : (removeOppositeIntersections (oppositeRows n) 1).length = 1 := by
    rw [← List.toFinset_card_of_nodup nodup, set,card_singleton]
  constructor
  · simp [Fin.sum_univ_two,oppositeRows,two_mul]
  · rw [Fin.sum_univ_two,firstOppositeRow_kept,one]
    simp [oppositeRows]

/-- At an original-budget half-bridge maximum, every one of the `p` paths
contributes an uncharged first incidence after pruning. -/
theorem localOrderMaximizer_oppositePruning_gain {n p k : ℕ} (hn : 0 < n) (large : 3 ≤ k)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible true k paths)
    (maximal : ∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) →
      localOrderAdmissible true k other → (∑ i, (other i).length) ≤ ∑ i, (paths i).length) :
    (∑ i, (paths i).length) + p ≤ 2 * (∑ i, (removeOppositeIntersections paths i).length) := by
  have everything : univ.filter (fun i => paths i ≠ []) = univ := by
    apply filter_true_of_mem
    intro i _
    exact localOrderMaximizer_nonempty hn paths allowed maximal simple i
  simpa only [everything, card_univ, Fintype.card_fin] using
    removeOppositeIntersections_mass_with_nonempty_paths simple allowed large

end OnlineReachabilityPreservers
