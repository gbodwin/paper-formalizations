import OnlineReachabilityPreservers.FrozenFullReturnSupportedCover

/-! A limited erasure around width boundaries meets short-span crossed returns. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

variable {V I : Type*} [LinearOrder V] [Fintype V] [Fintype I]

/-- Mark the first `margin` positions in each noninitial width block. -/
noncomputable def widthBoundaryIncidences (rows : I → List V) (width margin : ℕ) :
    Finset (ListBlockIndex rows width × V) :=
  (pieceIncidences (splitListPaths rows width) univ).filter fun jv =>
    0 < jv.1.snd.val ∧ (rows jv.1.fst).idxOf jv.2 % width < margin

omit [Fintype V] [Fintype I] in
private theorem widthBlock_eq {rows : I → List V} {width : ℕ} {i j : ListBlockIndex rows width}
    (parent : i.fst = j.fst) (block : i.snd.val = j.snd.val) : i = j := by
  rcases i with ⟨i,a⟩
  rcases j with ⟨j,b⟩
  change i = j at parent
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext block)

/-- Each noninitial block charges at most `margin` erasures. Count them
against the length divided by the width in each original path. -/
theorem widthBoundaryIncidences_card_le (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    (width margin : ℕ) : (widthBoundaryIncidences rows width margin).card ≤
      (∑ i, (rows i).length / width) * margin := by
  classical
  let marked := widthBoundaryIncidences rows width margin
  let target := Σ i : I, Fin ((rows i).length / width) × Fin margin
  have markedFacts (jv : marked) :
      jv.val.2 ∈ splitListPaths rows width jv.val.1 ∧
        0 < jv.val.1.snd.val ∧ (rows jv.val.1.fst).idxOf jv.val.2 % width < margin := by
    have h := mem_filter.mp jv.property
    exact ⟨(mem_pieceIncidences.mp h.1).2,h.2⟩
  let place (jv : marked) : target :=
    ⟨jv.val.1.fst,⟨⟨jv.val.1.snd.val-1,by
      have inside := jv.val.1.snd.isLt
      change jv.val.1.snd.val < (rows jv.val.1.fst).toFinset.card/width+1 at inside
      rw [List.toFinset_card_of_nodup (simple jv.val.1.fst)] at inside
      have positive := (markedFacts jv).2.1
      omega⟩, ⟨(rows jv.val.1.fst).idxOf jv.val.2 % width,(markedFacts jv).2.2⟩⟩⟩
  have injective : Function.Injective place := by
    intro x y same
    have ⟨onX,positiveX,_⟩ := markedFacts x
    have ⟨onY,positiveY,_⟩ := markedFacts y
    have parent := congrArg Sigma.fst same
    have block := congrArg (fun z : target => z.snd.1.val) same
    have offset := congrArg (fun z : target => z.snd.2.val) same
    change x.val.1.fst = y.val.1.fst at parent
    change x.val.1.snd.val-1 = y.val.1.snd.val-1 at block
    change (rows x.val.1.fst).idxOf x.val.2 % width = (rows y.val.1.fst).idxOf y.val.2 % width at offset
    have sameBlock : x.val.1.snd.val = y.val.1.snd.val := by omega
    have pieceEqual := widthBlock_eq parent sameBlock
    have ⟨originalX,quotientX⟩ := mem_localPathBlock.mp onX
    have ⟨_,quotientY⟩ := mem_localPathBlock.mp onY
    have idxX := Nat.mod_add_div ((rows x.val.1.fst).idxOf x.val.2) width
    have idxY := Nat.mod_add_div ((rows y.val.1.fst).idxOf y.val.2) width
    rw [quotientX,sameBlock] at idxX
    have rowY : (rows y.val.1.fst).idxOf y.val.2 = (rows x.val.1.fst).idxOf y.val.2 :=
      congrArg (fun i => (rows i).idxOf y.val.2) parent.symm
    rw [quotientY,rowY] at idxY
    rw [rowY] at offset
    have vertexEqual : x.val.2 = y.val.2 := (List.idxOf_inj originalX).mp (by omega)
    exact Subtype.ext (Prod.ext pieceEqual vertexEqual)
  have count := Fintype.card_le_of_injective place injective
  simpa only [target,marked,Fintype.card_coe,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,sum_mul] using count

/-- These are exactly the return endpoints tested for the short-span
criterion. The distance is measured along the copied parent row. -/
def CrossedWidthReturnSpanLE (rows : I → List V) (width radius margin : ℕ) : Prop :=
  let pieces := splitListPaths rows width
  ∀ ⦃i j : ListBlockIndex rows width⦄ {d : ℕ}, i ≠ j → i.fst = j.fst → d ≤ radius →
    ∀ (v : Fin (d+1) → V) (a : Fin d → ListBlockIndex rows width),
      (∀ t, i.fst ≠ (a t).fst) → Function.Injective (fun t => (a t).fst) →
      v 0 ∈ pieces i → v (Fin.last d) ∈ pieces j →
      Before rows i.fst (v (Fin.last d)) (v 0) →
      (∀ t, Before pieces (a t) (v t.castSucc) (v t.succ)) →
      (rows i.fst).idxOf (v 0) ≤ (rows i.fst).idxOf (v (Fin.last d)) + margin

/-- A short backward span across two blocks puts its later endpoint within
the boundary margin. -/
theorem mem_widthBoundaryIncidences_of_parent_span (rows : I → List V) {width margin : ℕ}
    (positive : 0 < width) {i j : ListBlockIndex rows width} {laterVertex earlierVertex : V}
    (apart : i ≠ j) (same : i.fst = j.fst)
    (first : laterVertex ∈ splitListPaths rows width i) (last : earlierVertex ∈ splitListPaths rows width j)
    (backward : Before rows i.fst earlierVertex laterVertex)
    (bounds : (rows i.fst).idxOf laterVertex ≤ (rows i.fst).idxOf earlierVertex+margin) :
    (i,laterVertex) ∈ widthBoundaryIncidences rows width margin := by
  classical
  let x := (rows i.fst).idxOf laterVertex
  let y := (rows i.fst).idxOf earlierVertex
  have later : y < x := backward.2.2
  have onX : x/width = i.snd.val := (mem_localPathBlock.mp first).2
  have onY : y/width = j.snd.val := by
    dsimp only [y]
    rw [same]
    exact (mem_localPathBlock.mp last).2
  have unequal : j.snd.val ≠ i.snd.val := fun sameIndex => apart (widthBlock_eq same sameIndex.symm)
  have blockOrder := Nat.div_le_div_right (c := width) later.le
  rw [onX,onY] at blockOrder
  have separated : j.snd.val+1 ≤ i.snd.val := by omega
  have scaled := Nat.mul_le_mul_left width separated
  rw [Nat.mul_add,Nat.mul_one] at scaled
  have splitY := Nat.mod_add_div y width
  have splitX := Nat.mod_add_div x width
  rw [onY] at splitY
  rw [onX] at splitX
  have withinY := Nat.mod_lt y positive
  have near : x % width < margin := by omega
  apply mem_filter.mpr
  refine ⟨mem_pieceIncidences.mpr ⟨mem_univ _,first⟩,?_⟩
  change 0 < i.snd.val ∧ x % width < margin
  exact ⟨by omega,near⟩

/-- Delete the marked boundary to meet every tested short-span return. -/
theorem widthBoundaryIncidences_covers_short_span (rows : I → List V) {width radius margin : ℕ}
    (positive : 0 < width) (shortSpan : CrossedWidthReturnSpanLE rows width radius margin) :
    CrossedParentReturnIncidenceCover rows (splitListPaths rows width) Sigma.fst radius
      (widthBoundaryIncidences rows width margin) := by
  intro i j d apart same short v a other injective first last backward along
  exact Or.inl (mem_widthBoundaryIncidences_of_parent_span rows positive apart same first last backward
    (shortSpan apart same short v a other injective first last backward along))

/-- Scale the margin to charge the erased incidences against the
original mass. -/
theorem widthBoundaryIncidences_scaled_mass (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    {width margin scale : ℕ} (narrow : scale*margin ≤ width) :
    scale*(widthBoundaryIncidences rows width margin).card ≤ ∑ i, (rows i).length := by
  calc
    _ ≤ scale*((∑ i, (rows i).length / width) * margin) :=
      Nat.mul_le_mul_left scale (widthBoundaryIncidences_card_le rows simple width margin)
    _ = (∑ i, (rows i).length / width) * (scale*margin) := by ring
    _ ≤ (∑ i, (rows i).length / width) * width := Nat.mul_le_mul_left _ narrow
    _ ≤ _ := by
      rw [sum_mul]
      exact sum_le_sum (fun i _ => Nat.div_mul_le_self (rows i).length width)

/-- A margin of at most one third of the width charges at most a third
of the input incidences. -/
theorem widthBoundaryIncidences_third_mass (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    {width margin : ℕ} (narrow : 3*margin ≤ width) :
    3*(widthBoundaryIncidences rows width margin).card ≤ ∑ i, (rows i).length :=
  widthBoundaryIncidences_scaled_mass rows simple narrow

/-- The standard copies and width blocks pass the span test when every
crossed return of length at most `cutoff-5` spans at most `L/3` parent
positions, where `L` is the original path width. -/
def HasShortSpanCrossedWidthReturns {n p : ℕ} (rows : Fin p → List (Fin n)) (cutoff : ℕ) : Prop :=
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  CrossedWidthReturnSpanLE (splitListVertices rows D) L (cutoff-5) (L/3)

/-- A passing span test supplies the third-mass crossed-return cover. -/
theorem thirdMassCrossedReturnWidthCover_of_short_span {n p cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (hp : 0 < p) (long : p ≤ ∑ i, (rows i).length)
    (shortSpan : HasShortSpanCrossedWidthReturns rows cutoff) : HasThirdMassCrossedReturnWidthCover rows cutoff := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices rows D
  have positive : 0 < L := (four_average_width hp long).1
  refine ⟨widthBoundaryIncidences copies L (L/3),widthBoundaryIncidences_covers_short_span copies positive shortSpan,?_⟩
  have covered := widthBoundaryIncidences_third_mass copies
    (fun i => splitListVertices_simple rows D i (simple i)) (width := L) (margin := L/3) (by omega)
  change 3*(widthBoundaryIncidences copies L (L/3)).card ≤ M
  refine covered.trans ?_
  exact (sum_congr rfl (fun i _ => splitListVertices_length rows D i)).le

/-- The short-span criterion gives a frozen full witness with the same
cutoff, both original budgets, and one twenty-seventh of the mass. -/
theorem regularization_list_frozen_full_of_short_span_width_returns {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (large : 7 ≤ cutoff) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (span : 8*max n p < (∑ i, (paths i).length) → HasShortSpanCrossedWidthReturns paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 27*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_full_of_third_mass_width_return_cover paths simple free large hn hp dense long
    (fun high => thirdMassCrossedReturnWidthCover_of_short_span paths simple hp long (span high))

/-- The same span test gives distinct nonempty rows for feasible literal input. -/
theorem regularization_list_frozen_full_distinct_of_short_span_width_returns {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (large : 7 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (span : 8*max n p < (∑ i, (paths i).length) → HasShortSpanCrossedWidthReturns paths cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 27*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 27)
    paths distinct nonempty simple free (by omega) hn hp dense (by decide)
    (fun long => regularization_list_frozen_full_of_short_span_width_returns paths simple free large hn hp dense long span)

end OnlineReachabilityPreservers
