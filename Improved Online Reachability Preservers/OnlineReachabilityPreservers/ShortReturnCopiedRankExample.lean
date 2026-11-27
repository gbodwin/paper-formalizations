import OnlineReachabilityPreservers.ShortReturnRankedExcess

/-! Degree copying separates the first seven common vertices of two reversed rows. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

private def returnSpine : List (Fin 51) := List.ofFn fun i : Fin 21 => i.castLE (by decide)

/-- Two opposite rows with three singleton incidences between them for
each of their first seven vertices in the forward order. -/
def copiedRankExampleRows (i : Fin 23) : List (Fin 51) :=
  if i = 0 then returnSpine
  else if i = 22 then returnSpine.reverse
  else [⟨(i.val-1)/3, by have := i.isLt; omega⟩]

private theorem copiedRankExample_mass_simple :
    (∑ i, (copiedRankExampleRows i).length) = 63 ∧
      ∀ i, (copiedRankExampleRows i).Nodup := by decide +kernel

/-- The frozen degree and path widths of the mass-63 input are four and ten. -/
theorem copiedRankExample_widths :
    let M := ∑ i, (copiedRankExampleRows i).length
    M = 63 ∧ 4*M/51 = 4 ∧ 4*M/23 = 10 := by
  dsimp only
  rw [copiedRankExample_mass_simple.1]
  decide

private theorem before_pairwise {I V : Type*} [DecidableEq V] {rows : I → List V}
    {R : V → V → Prop} {i : I} {x y : V}
    (pairwise : (rows i).Pairwise R) (step : BeforeIn rows i x y) : R x y := by
  have xAt := List.idxOf_lt_length_of_mem step.1
  have yAt := List.idxOf_lt_length_of_mem step.2.1
  have ordered := List.pairwise_iff_getElem.mp pairwise _ _ xAt yAt step.2.2
  simpa only [List.getElem_idxOf] using ordered

private theorem copiedRankExample_steps {i : Fin 23} {x y : Fin 51}
    (step : BeforeIn copiedRankExampleRows i x y) :
    (i = 0 ∧ x < y) ∨ (i = 22 ∧ y < x) := by
  by_cases first : i = 0
  · subst i
    exact Or.inl ⟨rfl, before_pairwise (by decide +kernel) step⟩
  by_cases last : i = 22
  · subst i
    exact Or.inr ⟨rfl, before_pairwise (R := fun x y => y < x) (by decide +kernel) step⟩
  have singleton : copiedRankExampleRows i = [⟨(i.val-1)/3, by have := i.isLt; omega⟩] := by
    simp only [copiedRankExampleRows, ite_eq_right first, ite_eq_right last]
  have same : x = y := (List.mem_singleton.mp (singleton ▸ step.1)).trans
    (List.mem_singleton.mp (singleton ▸ step.2.1)).symm
  exact (listBefore_ne step same).elim

/-- Only the two long rows have comparisons, and their orders are opposite. -/
theorem copiedRankExample_fullFree (cutoff : ℕ) : BridgeFree (BeforeIn copiedRankExampleRows) cutoff := by
  intro j _
  refine ⟨fun b => ?_⟩
  rcases copiedRankExample_steps b.riverStep with ⟨river, forward⟩ | ⟨river, backward⟩
  · have decreasing (s : Fin (j+2)) : b.vertex s ≤ b.vertex 0 := by
      induction s using Fin.induction with
      | zero => exact le_rfl
      | succ s ih =>
        rcases copiedRankExample_steps (b.arcStep s) with ⟨arc, _⟩ | ⟨_, step⟩
        · exact (b.river_ne_arc s (river.trans arc.symm)).elim
        · exact step.le.trans ih
    exact forward.not_ge (decreasing _)
  · have increasing (s : Fin (j+2)) : b.vertex 0 ≤ b.vertex s := by
      induction s using Fin.induction with
      | zero => exact le_rfl
      | succ s ih =>
        rcases copiedRankExample_steps (b.arcStep s) with ⟨_, step⟩ | ⟨arc, _⟩
        · exact ih.trans step.le
        · exact (b.river_ne_arc s (river.trans arc.symm)).elim
    exact backward.not_ge (increasing _)

private theorem copiedRankExample_reverse_at_zero :
    ∀ x : Fin 51, x ∈ copiedRankExampleRows 0 → x ≠ 0 →
      BeforeIn copiedRankExampleRows 0 0 x ∧ BeforeIn copiedRankExampleRows 22 x 0 := by
  unfold BeforeIn
  decide +kernel

private theorem copiedRankExample_back_same_vertices :
    (copiedRankExampleRows 22).toFinset = (copiedRankExampleRows 0).toFinset := by
  simp [copiedRankExampleRows]

private theorem copiedRankExample_zero_on_both (i : Fin 23) (either : i = 0 ∨ i = 22) :
    (0 : Fin 51) ∈ (copiedRankExampleRows i).toFinset := by
  rcases either with rfl | rfl
  · decide +kernel
  · rw [copiedRankExample_back_same_vertices]
    decide +kernel

private theorem same_component_of_reversed_comparisons {I V : Type*}
    [Fintype I] [LinearOrder V] [Fintype V] {rows : I → List V}
    {i j : I} {x y : V} (forward : BeforeIn rows i x y) (backward : BeforeIn rows j y x) :
    SameComponent (shortReturnRowGraph rows 7 i) x y := by
  let G := listPiecePrecedenceGraph rows
  have edge : Edge G y x := listPiecePrecedenceGraph_edge.mpr ⟨j, backward⟩
  have back : y ∈ reachIn G x 4 :=
    (reachIn_succ (G := G) (t := x) (u := y) (k := 3)).mpr
      (Or.inr ⟨x, edge, target_mem_reachIn G x 3⟩)
  exact ⟨.single (shortReturnRowGraph_edge.mpr (.inl ⟨forward, back⟩)),
    .single (shortReturnRowGraph_edge.mpr (.inr ⟨forward, back⟩))⟩

private theorem copiedRankExample_component (i : Fin 23) (either : i = 0 ∨ i = 22) :
    shortReturnRowComponent copiedRankExampleRows 7 i 0 = (copiedRankExampleRows i).toFinset := by
  ext x
  refine ⟨fun on => (mem_filter.mp on).1, fun on => ?_⟩
  apply mem_filter.mpr
  refine ⟨on, ?_⟩
  by_cases atZero : x = 0
  · subst x
    rfl
  have onForward : x ∈ (copiedRankExampleRows 0).toFinset := by
    rcases either with rfl | rfl
    · exact on
    · exact copiedRankExample_back_same_vertices ▸ on
  obtain ⟨forward, backward⟩ := copiedRankExample_reverse_at_zero x (List.mem_toFinset.mp onForward) atZero
  apply componentLabel_eq.mpr
  rcases either with rfl | rfl
  · exact (same_component_of_reversed_comparisons forward backward).symm
  · exact same_component_of_reversed_comparisons backward forward

private theorem path_excess_of_two_components {I V : Type*}
    [Fintype I] [LinearOrder V] [Fintype V] {rows : I → List V} {width cutoff : ℕ}
    {i j : I} (different : i ≠ j) {x y : V} (onX : x ∈ rows i) (onY : y ∈ rows j)
    {small large : ℕ} (boundX : small ≤ (shortReturnRowComponent rows cutoff i x).card)
    (boundY : large ≤ (shortReturnRowComponent rows cutoff j y).card) :
    small-width + (large-width) ≤ shortReturnPathExcessMass rows width cutoff := by
  classical
  let excess (r : I) := ∑ group ∈ linkedGroupComponents (rows r).toFinset
    (shortReturnRowGraph rows cutoff r), (group.card - width)
  have bounds {r : I} {z : V} (on : z ∈ rows r) :
      (shortReturnRowComponent rows cutoff r z).card - width ≤ excess r :=
    single_le_sum (f := fun group : Finset V => group.card - width)
      (fun _ _ => Nat.zero_le _) (mem_image_of_mem _ (List.mem_toFinset.mpr on))
  calc
    _ ≤ excess i + excess j := Nat.add_le_add ((Nat.sub_le_sub_right boundX width).trans (bounds onX))
      ((Nat.sub_le_sub_right boundY width).trans (bounds onY))
    _ = ∑ r ∈ ({i, j} : Finset I), excess r := (sum_pair different).symm
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)

/-- Both original long rows are oversized components of size 21.
Their combined excess of 22 exceeds one third of the input mass. -/
theorem copiedRankExample_original_excess :
    63 < 3*shortReturnPathExcessMass copiedRankExampleRows 10 7 := by
  have count (i : Fin 23) (either : i = 0 ∨ i = 22) :
      21 ≤ (shortReturnRowComponent copiedRankExampleRows 7 i 0).card := by
    rw [copiedRankExample_component i either]
    rcases either with rfl | rfl <;> decide +kernel
  have total : 22 ≤ shortReturnPathExcessMass copiedRankExampleRows 10 7 :=
    path_excess_of_two_components (cutoff := 7) (width := 10) (i := 0) (j := 22)
      (by decide) (List.mem_toFinset.mp (copiedRankExample_zero_on_both 0 (.inl rfl)))
      (List.mem_toFinset.mp (copiedRankExample_zero_on_both 22 (.inr rfl)))
      (count 0 (.inl rfl)) (count 22 (.inr rfl))
  exact (by decide : 63 < 3*22).trans_le (Nat.mul_le_mul_left 3 total)

abbrev CopiedRankExampleVertex := ListVertexBlockIndex copiedRankExampleRows 4

abbrev copiedRankExampleCopies := splitListVertices copiedRankExampleRows 4

private def copiedRankExampleRank (v : CopiedRankExampleVertex) : ℕ :=
  if v.fst.val < 7 then
    if v.snd.val = 0 then v.fst.val else 14 - v.fst.val
  else 7

private def copiedRankExampleKey (v : CopiedRankExampleVertex) : ℕ × ℕ :=
  (copiedRankExampleRank v, v.fst.val)

private def copiedRankExampleKeys (i : Fin 23) : List (ℕ × ℕ) :=
  if i = 0 then List.ofFn fun v : Fin 21 => (min v.val 7, v.val)
  else if i = 22 then (List.ofFn fun v : Fin 21 =>
    (if v.val < 7 then 14 - v.val else 7, v.val)).reverse
  else let v := (i.val-1)/3; [(v,v)]

private def copiedRankExampleKeep (key : ℕ × ℕ) : Bool :=
  decide (key.1 ≠ 7 ∨ key.2 < 17)

private def copiedRankExampleSelection (i : Fin 23) : Finset CopiedRankExampleVertex :=
  ((copiedRankExampleCopies i).filter (copiedRankExampleKeep ∘ copiedRankExampleKey)).toFinset

private theorem copiedRankExample_copy_simple (i : Fin 23) : (copiedRankExampleCopies i).Nodup :=
  splitListVertices_simple copiedRankExampleRows 4 i (copiedRankExample_mass_simple.2 i)

private theorem copiedRankExample_selection_subset (i : Fin 23) :
    copiedRankExampleSelection i ⊆ (copiedRankExampleCopies i).toFinset := by
  unfold copiedRankExampleSelection
  rw [List.toFinset_filter]
  exact filter_subset _ _

set_option maxRecDepth 4096 in
private theorem copiedRankExample_keys_eq (i : Fin 23) :
    (copiedRankExampleCopies i).map copiedRankExampleKey = copiedRankExampleKeys i := by
  fin_cases i <;> decide +kernel

private theorem copiedRankExample_filter_length (i : Fin 23) (test : ℕ × ℕ → Bool) :
    ((copiedRankExampleCopies i).filter (test ∘ copiedRankExampleKey)).length =
      ((copiedRankExampleKeys i).filter test).length := by
  rw [← copiedRankExample_keys_eq, List.filter_map, List.length_map]

private theorem copiedRankExample_ordered (i : Fin 23) :
    (copiedRankExampleCopies i).Pairwise (fun x y => copiedRankExampleRank x ≤ copiedRankExampleRank y) := by
  have keys : ∀ j : Fin 23, (copiedRankExampleKeys j).Pairwise (fun x y => x.1 ≤ y.1) := by
    decide +kernel
  have sequence := keys i
  rw [← copiedRankExample_keys_eq, List.pairwise_map] at sequence
  exact sequence

private theorem copiedRankExample_count :
    (∑ i, (copiedRankExampleSelection i).card) = 55 ∧
      ∀ (i : Fin 23) (a : Fin 15),
        ((copiedRankExampleSelection i).filter fun v => copiedRankExampleRank v = a.val).card ≤ 10 := by
  have count : (∑ i, ((copiedRankExampleKeys i).filter copiedRankExampleKeep).length) = 55 := by
    decide +kernel
  have each : ∀ (i : Fin 23) (a : Fin 15),
      ((copiedRankExampleKeys i).filter fun key => decide (key.1 = a.val) && copiedRankExampleKeep key).length ≤ 10 := by
    decide +kernel
  constructor
  · rw [← count]
    apply sum_congr rfl
    intro i _
    unfold copiedRankExampleSelection
    rw [List.toFinset_card_of_nodup ((copiedRankExample_copy_simple i).filter _),
      copiedRankExample_filter_length]
  · intro i a
    unfold copiedRankExampleSelection
    rw [List.filter_toFinset, List.toFinset_card_of_nodup (((copiedRankExample_copy_simple i).filter _).filter _),
      List.filter_filter]
    change ((copiedRankExampleCopies i).filter
      ((fun key : ℕ × ℕ => decide (key.1 = a.val) && copiedRankExampleKeep key) ∘ copiedRankExampleKey)).length ≤ 10
    rw [copiedRankExample_filter_length]
    exact each i a

private theorem copiedRankExample_small (i : Fin 23) (a : ℕ) :
    ((copiedRankExampleSelection i).filter fun v => copiedRankExampleRank v = a).card ≤ 10 := by
  by_cases within : a < 15
  · exact copiedRankExample_count.2 i ⟨a, within⟩
  have atMost (v : CopiedRankExampleVertex) : copiedRankExampleRank v < 15 := by
    unfold copiedRankExampleRank
    split_ifs <;> omega
  have empty : (copiedRankExampleSelection i).filter (fun v => copiedRankExampleRank v = a) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v on
    exact within ((mem_filter.mp on).2 ▸ atMost v)
  simp [empty]

/-- After copying, the clipped path excess is at most eight at every
cutoff. The certificate uses the comparison ranks of the actual copies. -/
theorem copiedRankExample_copied_excess (cutoff : ℕ) :
    shortReturnPathExcessMass copiedRankExampleCopies 10 cutoff ≤ 8 := by
  have bound := shortReturnPathExcessMass_add_ranked_subsets_le copiedRankExampleCopies
    copiedRankExample_copy_simple 10 cutoff
    copiedRankExampleRank (fun {i _ _} step =>
      before_pairwise (R := fun x y => copiedRankExampleRank x ≤ copiedRankExampleRank y)
        (copiedRankExample_ordered i) step)
    copiedRankExampleSelection copiedRankExample_selection_subset copiedRankExample_small
  simp only [copiedRankExample_count.1, splitListVertices_length, copiedRankExample_mass_simple.1] at bound
  omega

/-- The copied excess certifies a frozen full witness at any chosen cutoff. -/
theorem copiedRankExample_full_frozen (cutoff : ℕ) :
    ∃ n' ≤ 51, ∃ p' ≤ 23, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (BeforeIn clean) cutoff ∧
      63 ≤ 36*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 63 ∧ frozenListCaps 51 23 63 clean := by
  have mass := copiedRankExample_mass_simple.1
  have dense : 51 ≤ ∑ i, (copiedRankExampleRows i).length := by rw [mass]; decide
  have long : 23 ≤ ∑ i, (copiedRankExampleRows i).length := by rw [mass]; decide
  have result := regularization_list_frozen_full_of_small_copied_path_excess (k := cutoff) copiedRankExampleRows
    copiedRankExample_mass_simple.2 (copiedRankExample_fullFree cutoff) (by decide) (by decide) dense long (by
      dsimp only
      rw [mass, (show 4*63/51 = 4 by decide), (show 4*63/23 = 10 by decide)]
      exact (Nat.mul_le_mul_left 3 (copiedRankExample_copied_excess cutoff)).trans (by decide))
  simpa only [mass] using result

end OnlineReachabilityPreservers.SourceAudit
