import OnlineReachabilityPreservers.FrozenFullSixConflicts
import OnlineReachabilityPreservers.FrozenFullSixRepair
import OnlineReachabilityPreservers.FrozenHalfFourCleaning

/-! Frozen-average cleaning through full cutoff six for simple paths. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

variable {n p : ℕ}

private theorem crossedOpposite_source_heavy {paths : Fin p → List (Fin n)} (width : ℕ)
    {a b : ListBlockIndex paths width × Fin n}
    (edge : CrossedOppositeConflict paths (splitListPaths paths width) Sigma.fst a b) :
    a ∈ pieceIncidences (splitListPaths paths width) (heavyPieces paths width) := by
  refine mem_pieceIncidences.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,edge.source_mem⟩
  obtain ⟨_,early,_,different,same,_,first,last,_,_⟩ := edge
  by_contra h
  have short : (paths a.1.fst).length ≤ width := Nat.le_of_not_gt h
  have earlyShort : (paths early.fst).length ≤ width := same.symm ▸ short
  exact different (same_path_block same
    ((short_block_zero earlyShort first).trans (short_block_zero short last).symm))

private theorem full_six_of_moderate_overlong_mass (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) 6)
    (hn : 0 < n) (hp : 0 < p)
    (largeN : 8*n ≤ ∑ i, (paths i).length) (largeP : 8*p ≤ ∑ i, (paths i).length)
    (moderate : let M := ∑ i, (paths i).length; 50*listMassAboveWidth paths (4*M/p) ≤ 29*M)
    (excess : let M := ∑ i, (paths i).length; 12*M ≤ 25*listLengthExcess paths (4*M/p)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) 6 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let L := 4*M/p
  let J := ListBlockIndex paths L
  let pieces := splitListPaths paths L
  let heavy := heavyPieces paths L
  let light := lightPieces paths L
  let edge := CrossedOppositeConflict paths pieces Sigma.fst
  refine regularization_list_frozen_after_moderate_width_cut (half := false) (k := 6) paths simple
    (by decide) hn hp largeN largeP moderate excess ?_
  dsimp only
  intro separate covers heavyFits lightRoom hyp
  have pieceSimple (i : J) : (pieces i).Nodup := List.filter_sublist.nodup (simple i.fst)
  have steps {i : J} {x y : Fin n} : Before pieces i x y → Before paths i.fst x y := splitPath_step simple
  have apart {i j : J} {x : Fin n} :
      i ≠ j → i.fst = j.fst → x ∈ pieces i → x ∈ pieces j → False := splitListPaths_disjoint
  have three : BridgeFree (Before paths) 3 := fun _ small => free (small.trans (by decide))
  have target {a b : J × Fin n} (ab : edge a b) : b ∈ pieceIncidences pieces univ :=
    mem_pieceIncidences.mpr ⟨mem_univ _,ab.target_mem⟩
  obtain ⟨deleted,kept,coverCut,countK,big⟩ := oppositeCut_repair_budget (edge := edge) pieceSimple
    heavy light separate covers (fun {_ _} => crossedOpposite_source_heavy L)
    (fun {_ _} => target) (fun _ h => h.ne rfl)
    (fun {_ _ _} ab ac => CrossedOppositeConflict.out_unique three (fun {_ _ _} => steps)
      (fun {_ _ _} => apart) ab ac)
    (fun {_ _ _} ab cb => CrossedOppositeConflict.in_unique three (fun {_ _ _} => steps)
      (fun {_ _ _} => apart) ab cb) heavyFits lightRoom hyp
  have filteredFree := eraseOppositeCutConflicts_fullFree free pieceSimple (fun {_ _ _} => steps)
    (fun {_ _ _} => apart) (fun {_ _} => listBlocks_ordered paths L)
    deleted (fun {_ _} => coverCut)
  refine ⟨deleted,kept,filteredFree,countK,?_⟩
  rcases big with heavyEnough | twoSets
  · exact Or.inl heavyEnough
  · right
    let B := ∑ i : J, (pieces i).length
    let K := ∑ i ∈ kept, (erasePieceIncidences pieces deleted i).length
    have retained : 13*B ≤ 25*K := twoSets
    change 337*B ≤ 650*K
    calc
      _ ≤ 338*B := Nat.mul_le_mul_right B (by decide)
      _ = 26*(13*B) := by ring
      _ ≤ 26*(25*K) := Nat.mul_le_mul_left 26 retained
      _ = _ := by ring

/-- Every simple full-six-free family with mass at least both positive
budgets admits a full-six-free witness with all four original-average caps. -/
theorem regularization_list_frozen_full_six (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) 6)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) 6 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_four_or_six false paths simple free hn hp dense long
    (full_six_of_moderate_overlong_mass paths simple free hn hp)

/-- At full cutoff six, the original caps hold for a constant fraction
of the unrestricted indexed maximum on positive budgets. -/
theorem localOrderExtremal_frozen_full_six (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (Before paths) 6 ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) 6 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) 6 ∧
        M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p 6 false hn hp
  exact ⟨paths,simple,free,maximal,regularization_list_frozen_full_six paths simple free hn hp dense long⟩

end OnlineReachabilityPreservers
