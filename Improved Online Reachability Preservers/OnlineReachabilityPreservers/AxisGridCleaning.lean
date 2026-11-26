import OnlineReachabilityPreservers.HalfGridCleaning

/-! Frozen half-bridge cleaning with grids of any coordinate dimension. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

abbrev AxisGridLabel (m w : ℕ) := Fin (m+2) ×ₗ Fin (w^m)
abbrev AxisGridVertex (m w : ℕ) := Fin (w^(m+1))

private noncomputable def tupleCode (d w : ℕ) : (Fin d → Fin w) ≃ Fin (w^d) :=
  Fintype.equivFinOfCardEq (by simp)

private def axisGridDir {m w : ℕ} (i : AxisGridLabel m w) : Fin (m+2) := (ofLex i).1

private def gridAxis {m : ℕ} (d : Fin (m+2)) : Fin (m+1) :=
  if h : d.val < m+1 then ⟨d.val,h⟩ else Fin.last m

private theorem gridAxis_last {m : ℕ} : gridAxis (Fin.last (m+1)) = Fin.last m := by
  simp [gridAxis]

private theorem gridAxis_val_of_forward {m : ℕ} (d : Fin (m+2)) (forward : d ≠ Fin.last (m+1)) :
    (gridAxis d).val = d.val := by
  have notLast : d.val ≠ m+1 := fun h => forward (Fin.ext h)
  have small : d.val < m+1 := by omega
  simp [gridAxis,small]

private theorem gridDir_lt_last_iff {m : ℕ} (d : Fin (m+2)) :
    d.val < m ↔ gridAxis d ≠ Fin.last m := by
  by_cases reverse : d = Fin.last (m+1)
  · subst d
    simp [gridAxis_last]
  · have axisVal := gridAxis_val_of_forward d reverse
    have small := (gridAxis d).isLt
    rw [axisVal] at small
    constructor
    · intro high equal
      have value := congrArg Fin.val equal
      change (gridAxis d).val = m at value
      omega
    · intro notLast
      have valNot : (gridAxis d).val ≠ m := fun equal => notLast (Fin.ext equal)
      omega

private theorem gridAxis_and_orientation_injective {m : ℕ} {d e : Fin (m+2)}
    (axes : gridAxis d = gridAxis e)
    (orientation : (d = Fin.last (m+1)) ↔ (e = Fin.last (m+1))) : d = e := by
  by_cases reverse : d = Fin.last (m+1)
  · exact reverse.trans (orientation.mp reverse).symm
  · have eForward : e ≠ Fin.last (m+1) := fun back => reverse (orientation.mpr back)
    apply Fin.ext
    rw [← gridAxis_val_of_forward d reverse, ← gridAxis_val_of_forward e eForward, axes]

private noncomputable def gridTail {m w : ℕ} (i : AxisGridLabel m w) : Fin m → Fin w :=
  (tupleCode m w).symm (ofLex i).2

private noncomputable def gridCoord {m w : ℕ} (v : AxisGridVertex m w) : Fin (m+1) → Fin w :=
  (tupleCode (m+1) w).symm v

private noncomputable def axisGridAt {m w : ℕ} (i : AxisGridLabel m w) (j : Fin w) :
    AxisGridVertex m w :=
  tupleCode (m+1) w ((gridAxis (axisGridDir i)).insertNth
    (if axisGridDir i = Fin.last (m+1) then j.rev else j) (gridTail i))

/-- Each row varies one coordinate and leaves all the other coordinates fixed. -/
noncomputable def axisGridRows (m w : ℕ) (i : AxisGridLabel m w) : List (AxisGridVertex m w) :=
  List.ofFn (axisGridAt i)

private theorem axisGridAt_on_axis {m w : ℕ} (i : AxisGridLabel m w) (j : Fin w) :
    gridCoord (axisGridAt i j) (gridAxis (axisGridDir i)) =
      if axisGridDir i = Fin.last (m+1) then j.rev else j := by
  simp [gridCoord,axisGridAt,Fin.insertNth_apply_same]

private theorem axisGridAt_off_axis {m w : ℕ} (i : AxisGridLabel m w)
    (j : Fin w) (a : Fin m) :
    gridCoord (axisGridAt i j) ((gridAxis (axisGridDir i)).succAbove a) = gridTail i a := by
  simp [gridCoord,axisGridAt,Fin.insertNth_apply_succAbove]

theorem axisGridRows_simple {m w : ℕ} (i : AxisGridLabel m w) : (axisGridRows m w i).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b equal
  have value := congrArg (fun v : AxisGridVertex m w => gridCoord v (gridAxis (axisGridDir i))) equal
  rw [axisGridAt_on_axis,axisGridAt_on_axis] at value
  by_cases reverse : axisGridDir i = Fin.last (m+1)
  · exact Fin.rev_injective (by simpa only [reverse,ite_true] using value)
  · simpa only [reverse,ite_false] using value

theorem axisGridRows_length {m w : ℕ} (i : AxisGridLabel m w) : (axisGridRows m w i).length = w := by
  simp [axisGridRows]

private theorem axisGridRows_index {m w : ℕ} (i : AxisGridLabel m w) (j : Fin w) :
    @List.idxOf (AxisGridVertex m w) instBEqOfDecidableEq (axisGridAt i j) (axisGridRows m w i) = j.val := by
  let _ : BEq (AxisGridVertex m w) := instBEqOfDecidableEq
  have inside : j.val < (axisGridRows m w i).length := (axisGridRows_length i).symm ▸ j.isLt
  simpa [axisGridRows] using (axisGridRows_simple i).idxOf_getElem (i := j.val) inside

private theorem axisGridRows_step {m w : ℕ} {i : AxisGridLabel m w} {a b : AxisGridVertex m w}
    (step : Before (axisGridRows m w) i a b) :
    (∀ j, j ≠ gridAxis (axisGridDir i) → gridCoord a j = gridCoord b j) ∧
    (if axisGridDir i = Fin.last (m+1)
      then gridCoord b (gridAxis (axisGridDir i)) < gridCoord a (gridAxis (axisGridDir i))
      else gridCoord a (gridAxis (axisGridDir i)) < gridCoord b (gridAxis (axisGridDir i))) := by
  obtain ⟨u,rfl⟩ := List.mem_ofFn.mp step.1
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp step.2.1
  have ordered := step.2.2
  rw [axisGridRows_index,axisGridRows_index] at ordered
  have finOrder : u < v := ordered
  constructor
  · intro j different
    obtain ⟨a,rfl⟩ := Fin.exists_succAbove_eq different
    rw [axisGridAt_off_axis,axisGridAt_off_axis]
  · rw [axisGridAt_on_axis,axisGridAt_on_axis]
    by_cases reverse : axisGridDir i = Fin.last (m+1)
    · simpa only [reverse,ite_true,Fin.rev_lt_rev] using finOrder
    · simpa only [reverse,ite_false] using finOrder

private theorem axisGridRows_eq_of_dir_and_line {m w : ℕ} {i j : AxisGridLabel m w}
    (directions : axisGridDir i = axisGridDir j)
    {u v : AxisGridVertex m w} (uOn : u ∈ axisGridRows m w i) (vOn : v ∈ axisGridRows m w j)
    (sameLine : ∀ a, a ≠ gridAxis (axisGridDir i) → gridCoord u a = gridCoord v a) : i = j := by
  obtain ⟨a,rfl⟩ := List.mem_ofFn.mp uOn
  obtain ⟨b,rfl⟩ := List.mem_ofFn.mp vOn
  apply ofLex.injective (Prod.ext directions ?_)
  apply (tupleCode m w).symm.injective
  change gridTail i = gridTail j
  funext c
  have equal := sameLine ((gridAxis (axisGridDir i)).succAbove c) (Fin.succAbove_ne _ _)
  rw [axisGridAt_off_axis, directions, axisGridAt_off_axis] at equal
  exact equal

private theorem gridAxis_ne_last_forward {m : ℕ} {d : Fin (m+2)} (notLast : gridAxis d ≠ Fin.last m) :
    d ≠ Fin.last (m+1) := fun reverse => notLast (reverse ▸ gridAxis_last)

/-- All axis directions increase except the second direction of the last
axis. The two directions on that last axis arrive after all other rows. -/
theorem axisGridRows_halfFree (m w k : ℕ) : HalfBridgeFree (Before (axisGridRows m w)) k := by
  intro s _ b earlier
  let along (i : AxisGridLabel m w) := gridAxis (axisGridDir i)
  let reverse (i : AxisGridLabel m w) := axisGridDir i = Fin.last (m+1)
  let coord (z : Fin (s+2)) (j : Fin (m+1)) := gridCoord (b.vertex z) j
  have steps {i u v} (h : Before (axisGridRows m w) i (b.vertex u) (b.vertex v)) :
      (∀ j, j ≠ along i → coord u j = coord v j) ∧
      (if reverse i then coord v (along i) < coord u (along i)
       else coord u (along i) < coord v (along i)) := axisGridRows_step h
  have increasing (j : Fin (m+1)) (notLast : j ≠ Fin.last m) : Monotone (fun z => coord z j) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have step := steps (b.arcStep i)
    by_cases moves : j = along (b.arc i)
    · have nonLast : along (b.arc i) ≠ Fin.last m := fun equal => notLast (moves.trans equal)
      have noReverse : ¬ reverse (b.arc i) := gridAxis_ne_last_forward nonLast
      have rise := step.2
      rw [ite_eq_right noReverse,← moves] at rise
      exact rise.le
    · exact (step.1 j moves).le
  have fixed (j : Fin (m+1)) (notLast : j ≠ Fin.last m) (other : j ≠ along b.river)
      (z : Fin (s+2)) : coord z j = coord 0 j := by
    have equalEnds := (steps b.riverStep).1 j other
    exact le_antisymm ((increasing j notLast (Fin.le_last z)).trans_eq equalEnds.symm)
      (increasing j notLast (Fin.zero_le z))
  have arcAxes (i : Fin (s+1)) : along (b.arc i) = Fin.last m ∨ along (b.arc i) = along b.river := by
    by_cases isLast : along (b.arc i) = Fin.last m
    · exact Or.inl isLast
    · right
      by_contra other
      have rise := (steps (b.arcStep i)).2
      rw [ite_eq_right (gridAxis_ne_last_forward isLast),
        fixed _ isLast other i.castSucc, fixed _ isLast other i.succ] at rise
      exact lt_irrefl _ rise
  by_cases riverLast : along b.river = Fin.last m
  · have arcLast (i : Fin (s+1)) : along (b.arc i) = Fin.last m :=
      (arcAxes i).elim id (fun same => same.trans riverLast)
    have differentOrientation (i : Fin (s+1)) : ¬ (reverse b.river ↔ reverse (b.arc i)) := by
      intro same
      have directions := gridAxis_and_orientation_injective (riverLast.trans (arcLast i).symm) same
      apply b.river_ne_arc i
      apply axisGridRows_eq_of_dir_and_line directions b.riverStep.1 (b.arcStep i).1
      intro j off
      have notLast : j ≠ Fin.last m := riverLast ▸ off
      exact (fixed j notLast off i.castSucc).symm
    by_cases riverReversed : reverse b.river
    · have arcForward (i : Fin (s+1)) : ¬ reverse (b.arc i) := fun back =>
        differentOrientation i (iff_of_true riverReversed back)
      have mono : Monotone (fun z => coord z (Fin.last m)) := by
        apply Fin.monotone_iff_le_succ.mpr
        intro i
        have rise := (steps (b.arcStep i)).2
        rw [ite_eq_right (arcForward i),arcLast i] at rise
        exact rise.le
      have fall := (steps b.riverStep).2
      rw [ite_eq_left riverReversed,riverLast] at fall
      exact (not_lt_of_ge (mono (Fin.zero_le _))) fall
    · have arcBack (i : Fin (s+1)) : reverse (b.arc i) := by
        by_contra forward
        exact differentOrientation i (iff_of_false riverReversed forward)
      have anti : Antitone (fun z => coord z (Fin.last m)) := by
        apply Fin.antitone_iff_succ_le.mpr
        intro i
        have fall := (steps (b.arcStep i)).2
        rw [ite_eq_left (arcBack i),arcLast i] at fall
        exact fall.le
      have rise := (steps b.riverStep).2
      rw [ite_eq_right riverReversed,riverLast] at rise
      exact (not_lt_of_ge (anti (Fin.zero_le _))) rise
  · let i := Fin.last s
    have endIndex : i.succ = Fin.last (s+1) := Fin.succ_last _
    have lastAxis : along (b.arc i) = Fin.last m := by
      rcases arcAxes i with last | same
      · exact last
      · have forward : ¬ reverse b.river := gridAxis_ne_last_forward riverLast
        have nonLast : along (b.arc i) ≠ Fin.last m := fun equal => riverLast (same.symm.trans equal)
        have arcForward : ¬ reverse (b.arc i) := gridAxis_ne_last_forward nonLast
        have directions := gridAxis_and_orientation_injective same.symm (iff_of_false forward arcForward)
        have lastOnArc := (b.arcStep i).2.1
        rw [endIndex] at lastOnArc
        exact (b.river_ne_arc i (axisGridRows_eq_of_dir_and_line directions
          b.riverStep.2.1 lastOnArc (fun _ _ => rfl))).elim
    have riverFirst : b.river < b.arc i := Prod.Lex.lt_iff.mpr (Or.inl (by
      change (axisGridDir b.river).val < (axisGridDir (b.arc i)).val
      have early := (gridDir_lt_last_iff (axisGridDir b.river)).2 riverLast
      have late : ¬ (axisGridDir (b.arc i)).val < m := fun low =>
        (gridDir_lt_last_iff (axisGridDir (b.arc i))).1 low lastAxis
      omega))
    exact earlier.asymm riverFirst

private theorem axisGridRows_mem {m w : ℕ} {i : AxisGridLabel m w} {v : AxisGridVertex m w} :
    v ∈ axisGridRows m w i ↔
      gridTail i = (gridAxis (axisGridDir i)).removeNth (gridCoord v) := by
  constructor
  · intro inside
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp inside
    exact funext fun a => (axisGridAt_off_axis i j a).symm
  · intro tails
    let axis := gridAxis (axisGridDir i)
    let value := gridCoord v axis
    let t := if axisGridDir i = Fin.last (m+1) then value.rev else value
    refine List.mem_ofFn.mpr ⟨t,?_⟩
    apply (tupleCode (m+1) w).symm.injective
    change gridCoord (axisGridAt i t) = gridCoord v
    funext j
    by_cases changes : j = axis
    · rw [changes,axisGridAt_on_axis]
      by_cases reverse : axisGridDir i = Fin.last (m+1)
      · simp [t,value,reverse]
      · simp [t,value,reverse]
    · obtain ⟨a,rfl⟩ := Fin.exists_succAbove_eq changes
      rw [axisGridAt_off_axis]
      exact congrFun tails a

/-- Every point lies in exactly one row for each of the directions. -/
theorem axisGridRows_degree {m w : ℕ} (v : AxisGridVertex m w) :
    (occurrences (fun i => (axisGridRows m w i).toFinset) v).card = m+2 := by
  let rowOf (d : Fin (m+2)) : AxisGridLabel m w :=
    toLex (d,tupleCode m w ((gridAxis d).removeNth (gridCoord v)))
  let embed : Fin (m+2) ↪ AxisGridLabel m w := ⟨rowOf,fun _ _ eq => congrArg axisGridDir eq⟩
  have exactRows :
      occurrences (fun i => (axisGridRows m w i).toFinset) v = (univ : Finset (Fin (m+2))).map embed := by
    ext i
    simp only [mem_occurrences,List.mem_toFinset,axisGridRows_mem,mem_map,mem_univ,true_and]
    constructor
    · intro tails
      refine ⟨axisGridDir i,ofLex.injective (Prod.ext rfl ?_)⟩
      apply (tupleCode m w).symm.injective
      exact ((tupleCode m w).symm_apply_apply _).trans tails.symm
    · rintro ⟨d,rfl⟩
      exact (tupleCode m w).symm_apply_apply _
  rw [exactRows,card_map,card_univ,Fintype.card_fin]

private theorem axisGrid_copy_budget {m w n p M : ℕ} (hw : 0 < w)
    (vb : w^(m+1) ≤ n) (pb : (m+2)*w^m ≤ p)
    (massLow : (m+2)*n ≤ M) (massHigh : M ≤ 4*(m+2)*n) (widthLow : M ≤ 4*p*w) :
    ∃ t : ℕ, t*w^(m+1) ≤ n ∧ t*((m+2)*w^m) ≤ p ∧
      M ≤ 8*((m+2)*(t*w^(m+1))) ∧ (m+2)*(t*w^(m+1)) ≤ M := by
  let V := w^(m+1)
  let P := (m+2)*w^m
  let t := min (n/V) (p/P)
  have vFit : t*V ≤ n :=
    (Nat.mul_le_mul_right _ (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
  have pFit : t*P ≤ p :=
    (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
  have equalMass : (m+2)*V = P*w := by simp only [V,P,pow_succ,Nat.mul_assoc]
  refine ⟨t,vFit,pFit,?_,(Nat.mul_le_mul_left _ vFit).trans massLow⟩
  by_cases vertexSide : n/V ≤ p/P
  · have half := floorBlockMass (show 0 < V by dsimp [V]; positivity) vb
    have count : t = n/V := min_eq_left vertexSide
    rw [← count] at half
    calc
      M ≤ 4*(m+2)*n := massHigh
      _ ≤ (4*(m+2))*(2*(t*V)) := Nat.mul_le_mul_left _ half
      _ = 8*((m+2)*(t*V)) := by ring
  · have half := floorBlockMass (show 0 < P by dsimp [P]; positivity) pb
    have count : t = p/P := min_eq_right (le_of_not_ge vertexSide)
    rw [← count] at half
    calc
      M ≤ 4*p*w := widthLow
      _ = (4*w)*p := by ring
      _ ≤ (4*w)*(2*(t*P)) := Nat.mul_le_mul_left _ half
      _ = 8*(t*(P*w)) := by ring
      _ = 8*((m+2)*(t*V)) := by rw [← equalMass]; ring

/-- A grid of any positive width and any coordinate dimension gives a
single frozen-cap witness in the half-bridge mode if one block fits both
budgets, its degree lies between a quarter of the original mean and the
mean itself, and its path length meets the original caps. -/
theorem frozen_cleaning_axis_grid {m w n p M : ℕ} (hn : 0 < n) (hp : 0 < p) (hw : 0 < w)
    (vBudget : w^(m+1) ≤ n) (pBudget : (m+2)*w^m ≤ p)
    (massLow : (m+2)*n ≤ M) (massHigh : M ≤ 4*(m+2)*n)
    (widthLow : M ≤ 4*p*w) (widthHigh : p*w ≤ 4*M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ k, HalfBridgeFree (Before clean) k) ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨t,fitsV,fitsP,retained,upper⟩ := axisGrid_copy_budget hw vBudget pBudget massLow massHigh widthLow
  let copies (_ : Fin t) := axisGridRows m w
  let family := disjointListFamilies copies
  let N := Fintype.card (AxisGridVertex m w ×ₗ Fin t)
  let P := Fintype.card (AxisGridLabel m w ×ₗ Fin t)
  have basePaths : Fintype.card (AxisGridLabel m w) = (m+2)*w^m := by
    rw [← Fintype.card_congr (toLex : Fin (m+2) × Fin (w^m) ≃ AxisGridLabel m w),Fintype.card_prod]
    simp only [Fintype.card_fin]
  have countV : N = t*w^(m+1) := by
    unfold N
    rw [← Fintype.card_congr (toLex : AxisGridVertex m w × Fin t ≃ AxisGridVertex m w ×ₗ Fin t)]
    simp [Fintype.card_prod,Nat.mul_comm]
  have countP : P = t*((m+2)*w^m) := by
    unfold P
    rw [← Fintype.card_congr (toLex : AxisGridLabel m w × Fin t ≃ AxisGridLabel m w ×ₗ Fin t)]
    simp [Fintype.card_prod, basePaths, Nat.mul_comm]
  have simple : ∀ i, (family i).Nodup := disjointListFamilies_simple copies (fun _ => axisGridRows_simple)
  have legal (k : ℕ) : localOrderAdmissible true k family :=
    disjointListFamilies_admissible copies (fun _ => axisGridRows_simple) (fun _ => axisGridRows_halfFree m w k)
  have countMass : (∑ i, (family i).length) = (m+2)*(t*w^(m+1)) := by
    unfold family
    rw [disjointListFamilies_mass]
    simp [copies,axisGridRows_length,basePaths,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  let clean := relabelListPathsFin family
  obtain ⟨newSimple,_,mass,degree,length⟩ := relabelListPathsFin_spec family simple (legal 2)
  have allSizes (k : ℕ) : HalfBridgeFree (Before clean) k :=
    (relabelListPathsFin_spec family simple (legal k)).2.1
  have nPos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have pPos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  refine ⟨N,countV.trans_le fitsV,P,countP.trans_le fitsP,clean,newSimple,allSizes,?_,?_,?_,?_⟩
  · exact (congrArg (8*·) (mass.trans countMass)).symm ▸ retained
  · exact (mass.trans countMass).symm ▸ upper
  · intro v
    rw [degree,disjointListFamilies_degree]
    change (M:ℝ)/(4*(n:ℝ)) ≤ _ ∧ _ ≤ 4*(M:ℝ)/(n:ℝ)
    rw [axisGridRows_degree]
    constructor
    · apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
      exact_mod_cast (show M ≤ (m+2)*(4*n) by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using massHigh)
    · apply (le_div_iff₀ nPos).mpr
      exact_mod_cast (show (m+2)*n ≤ 4*M by omega)
  · intro i
    rw [length]
    have len : (family ((Fintype.orderIsoFinOfCardEq (AxisGridLabel m w ×ₗ Fin t) rfl) i)).length = w := by
      simp [family,disjointListFamilies,copies,axisGridRows_length]
    rw [len]
    constructor
    · apply (div_le_iff₀ (by positivity : 0 < 4*(p:ℝ))).mpr
      exact_mod_cast (show M ≤ w*(4*p) by simpa only [Nat.mul_comm] using widthLow)
    · apply (le_div_iff₀ pPos).mpr
      exact_mod_cast (show w*p ≤ 4*M by simpa only [Nat.mul_comm] using widthHigh)

/-- The original averages determine the width and the number of
directions. If one such grid fits, a witness retains at least one eighth
of that mass and meets all four original-average caps. -/
theorem frozen_cleaning_axis_grid_of_ceiling {n p M : ℕ} (hn : 0 < n) (hp : 0 < p)
    (dense : 2*n ≤ M) (long : p ≤ M) :
    let d := max 2 ((M+4*n-1)/(4*n))
    let w := (M+4*p-1)/(4*p)
    w^(d-1) ≤ n → d*w^(d-2) ≤ p →
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ k, HalfBridgeFree (Before clean) k) ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  intro d w vertices rows
  let c := (M+4*n-1)/(4*n)
  let m := d-2
  have two : 2 ≤ d := le_max_left 2 c
  have directions : m+2 = d := Nat.sub_add_cancel two
  have dimension : m+1 = d-1 := by omega
  have positive : 0 < M := hp.trans_le long
  obtain ⟨_,degreeCover,degreeBound⟩ := quarterMean_ceiling hn positive
  have enoughDegree : M ≤ 4*d*n := calc
    _ ≤ (4*n)*c := degreeCover
    _ ≤ (4*n)*d := Nat.mul_le_mul_left _ (le_max_right 2 c)
    _ = _ := by ring
  have degreeFits : d*n ≤ M := by
    change max 2 c*n ≤ M
    by_cases small : c ≤ 2
    · simpa only [max_eq_left small] using dense
    have raw : (4*n)*c ≤ M+4*n-1 := degreeBound
    rw [show (4*n)*c = 4*(c*n) by ring] at raw
    rw [max_eq_right (le_of_not_ge small)]
    omega
  obtain ⟨wPos,widthCover,widthBound⟩ := quarterMean_ceiling hp positive
  have widthFits : p*w ≤ 4*M := by
    change (4*p)*w ≤ M+4*p-1 at widthBound
    rw [Nat.mul_assoc] at widthBound
    omega
  exact frozen_cleaning_axis_grid (m := m) (w := w) hn hp wPos
    (by simpa only [dimension] using vertices) (by simpa only [directions] using rows)
    (by simpa only [directions] using degreeFits) (by simpa only [directions] using enoughDegree)
    widthCover widthFits

end OnlineReachabilityPreservers
