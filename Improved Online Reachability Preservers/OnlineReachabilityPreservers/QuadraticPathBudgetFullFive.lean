import OnlineReachabilityPreservers.PositiveMatchingDensity
import OnlineReachabilityPreservers.SaturatedLiteralFullFive

/-! For a row budget below the saturated range, keep complete cyclic
matchings in the one-way bipartite construction. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private def bandVertex {w : ℕ} (side : Fin 2) (offset : Fin w) : Fin (2*w) :=
  finProdFinEquiv (side,offset)

private theorem bandVertex_equal {w : ℕ} {s t : Fin 2} {x y : Fin w}
    (same : bandVertex s x = bandVertex t y) : s = t ∧ x = y := by
  simpa only [Prod.mk.injEq] using (finProdFinEquiv : Fin 2 × Fin w ≃ Fin (2*w)).injective same

private def bandCoords {w r : ℕ} (i : Fin (w*r)) : Fin w × Fin r :=
  finProdFinEquiv.symm i

/-- Include the first `r` cyclic perfect matchings between two layers
of width `w`, directed from the first layer to the second. -/
def cyclicPairBandRows {w r : ℕ} [NeZero w] (fits : r ≤ w) (i : Fin (w*r)) : List (Fin (2*w)) :=
  let coords := bandCoords i
  [bandVertex 0 coords.1,bandVertex 1 (coords.1+Fin.castLE fits coords.2)]

theorem cyclicPairBandRows_valid {w r : ℕ} [NeZero w] (fits : r ≤ w) (i : Fin (w*r)) :
    cyclicPairBandRows fits i ≠ [] ∧ (cyclicPairBandRows fits i).Nodup := by
  have apart : bandVertex 0 (bandCoords i).1 ≠
      bandVertex 1 ((bandCoords i).1+Fin.castLE fits (bandCoords i).2) := by
    intro same
    exact (by decide : (0 : Fin 2) ≠ 1) (bandVertex_equal same).1
  simp [cyclicPairBandRows,apart]

private theorem cyclicPairBandRows_step {w r : ℕ} [NeZero w] {fits : r ≤ w} {i : Fin (w*r)}
    {x y : Fin (2*w)} (step : Before (cyclicPairBandRows fits) i x y) :
    x = bandVertex 0 (bandCoords i).1 ∧
      y = bandVertex 1 ((bandCoords i).1+Fin.castLE fits (bandCoords i).2) := by
  let a := bandVertex 0 (bandCoords i).1
  let b := bandVertex 1 ((bandCoords i).1+Fin.castLE fits (bandCoords i).2)
  have apart : a ≠ b := fun eq => (by decide : (0 : Fin 2) ≠ 1) (bandVertex_equal eq).1
  have start : x = a ∨ x = b := by simpa only [cyclicPairBandRows,List.mem_cons,List.not_mem_nil,or_false] using step.1
  have finish : y = a ∨ y = b := by simpa only [cyclicPairBandRows,List.mem_cons,List.not_mem_nil,or_false] using step.2.1
  have order : [a,b].idxOf x < [a,b].idxOf y := step.2.2
  rcases start with rfl | rfl <;> rcases finish with rfl | rfl
  · exact (Nat.lt_irrefl _ order).elim
  · exact ⟨rfl,rfl⟩
  · simp [apart] at order
  · exact (Nat.lt_irrefl _ order).elim

/-- All matches are distinct. Any chain of two rows would join the
two disjoint layers at its internal vertex. -/
theorem cyclicPairBandRows_free {w r : ℕ} [NeZero w] (fits : r ≤ w) (k : ℕ) :
    BridgeFree (Before (cyclicPairBandRows fits)) k := by
  intro d _
  refine ⟨fun bridge => ?_⟩
  cases d with
  | zero =>
    have river := cyclicPairBandRows_step bridge.riverStep
    have arc := cyclicPairBandRows_step (bridge.arcStep 0)
    have left := (bandVertex_equal (river.1.symm.trans arc.1)).2
    have right := (bandVertex_equal (river.2.symm.trans arc.2)).2
    rw [left] at right
    have shift := Fin.castLE_injective fits (add_left_cancel right)
    exact bridge.river_ne_arc 0 ((finProdFinEquiv : Fin w × Fin r ≃ Fin (w*r)).symm.injective
      (Prod.ext left shift))
  | succ d =>
    have first := (cyclicPairBandRows_step (bridge.arcStep 0)).2
    have second := (cyclicPairBandRows_step (bridge.arcStep 1)).1
    exact (by decide : (1 : Fin 2) ≠ 0) (bandVertex_equal (first.symm.trans second)).1

/-- Each cyclic matching contributes one occurrence of every vertex. -/
theorem cyclicPairBandRows_degree {w r : ℕ} [NeZero w] (fits : r ≤ w) (x : Fin (2*w)) :
    (occurrences (fun i => (cyclicPairBandRows fits i).toFinset) x).card = r := by
  let location : Fin 2 × Fin w := finProdFinEquiv.symm x
  have onLayer : x = bandVertex location.1 location.2 := by
    simp only [bandVertex,Prod.mk.eta,location,Equiv.apply_symm_apply]
  let left (j : Fin r) : Fin w :=
    if location.1 = 0 then location.2 else location.2-Fin.castLE fits j
  let atShift : Fin r ↪ Fin (w*r) :=
    ⟨fun j => finProdFinEquiv (left j,j),fun _ _ same => congrArg Prod.snd (finProdFinEquiv.injective same)⟩
  have coords (j : Fin r) : bandCoords (atShift j) = (left j,j) := Equiv.symm_apply_apply _ _
  have membership (i : Fin (w*r)) :
      x ∈ cyclicPairBandRows fits i ↔ (bandCoords i).1 = left (bandCoords i).2 := by
    rw [onLayer]
    have sides : location.1 = 0 ∨ location.1 = 1 := by
      have bound := location.1.isLt
      rcases (show location.1.val = 0 ∨ location.1.val = 1 by omega) with eq | eq
      · exact Or.inl (Fin.ext eq)
      · exact Or.inr (Fin.ext eq)
    rcases sides with sideEq | sideEq
    · simp only [cyclicPairBandRows,List.mem_cons,List.not_mem_nil,or_false,left,sideEq,ite_true]
      constructor
      · rintro (same | same)
        · exact (bandVertex_equal same).2.symm
        · exact ((by decide : (0 : Fin 2) ≠ 1) (bandVertex_equal same).1).elim
      · intro same
        exact Or.inl (congrArg (bandVertex 0) same.symm)
    · have oneNotZero : (1 : Fin 2) ≠ 0 := by decide
      simp only [cyclicPairBandRows,List.mem_cons,List.not_mem_nil,or_false,left,sideEq,oneNotZero,ite_false]
      constructor
      · rintro (same | same)
        · exact ((by decide : (1 : Fin 2) ≠ 0) (bandVertex_equal same).1).elim
        · exact (eq_sub_iff_add_eq).mpr (bandVertex_equal same).2.symm
      · intro same
        exact Or.inr (congrArg (bandVertex 1) ((eq_sub_iff_add_eq).mp same).symm)
  have index : occurrences (fun i => (cyclicPairBandRows fits i).toFinset) x = univ.map atShift := by
    ext i
    simp only [mem_occurrences,List.mem_toFinset,membership,mem_map,mem_univ,true_and]
    constructor
    · intro same
      refine ⟨(bandCoords i).2,?_⟩
      apply (finProdFinEquiv : Fin w × Fin r ≃ Fin (w*r)).symm.injective
      rw [show finProdFinEquiv.symm (atShift (bandCoords i).2) = _ from coords _,← same]
      rfl
    · rintro ⟨j,rfl⟩
      rw [coords]
  rw [index,card_map,card_univ,Fintype.card_fin]

/-- The matching band has one row for each chosen left vertex and
shift, with exactly two incidences per row. -/
theorem cyclicPairBandRows_mass {w r : ℕ} [NeZero w] (fits : r ≤ w) :
    (∑ i, (cyclicPairBandRows fits i).length) = 2*(w*r) := by
  have len (i : Fin (w*r)) : (cyclicPairBandRows fits i).length = 2 := rfl
  simp [len,Nat.mul_comm]

/-- Keep complete cyclic matchings within both the row and mass budgets.
The row bound accounts for a partial matching and for singleton rows
in the input. All degrees satisfy the original caps. -/
theorem frozen_full_cyclic_band_of_row_budget {n p M : ℕ} (nLarge : 6 ≤ n)
    (rowLower : 3*n ≤ p) (rowUpper : 3*p ≤ 4*n*(n/2))
    (massLower : 2*p ≤ M+n) (massUpper : M ≤ 3*p) :
    ∃ q ≤ p, ∃ rows : Fin q → List (Fin (2*(n/2))), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ (∀ k, BridgeFree (Before rows) k) ∧
      (∑ i, (rows i).length) = 2*q ∧ 2*min p ((n/2)^2) ≤ 2*q+2*(n/2)+n+1 ∧
      (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let w := n/2
  let budget := min p (M/2)
  let r := min w (budget/w)
  have wLarge : 3 ≤ w := by dsimp [w]; omega
  have wPos : 0 < w := by omega
  have nFit : 2*w ≤ n := by dsimp [w]; omega
  have nNear : n ≤ 2*w+1 := by dsimp [w]; omega
  have budgetFit : budget ≤ p := min_le_left _ _
  have budgetMass : 2*budget ≤ M :=
    (Nat.mul_le_mul_left _ (min_le_right _ _)).trans (Nat.mul_div_le _ _)
  have budgetNear : 2*p ≤ 2*budget+n+1 := by
    by_cases whole : p ≤ M/2
    · simp only [budget,min_eq_left whole]
      omega
    · simp only [budget,min_eq_right (by omega : M/2 ≤ p)]
      omega
  have rLarge : 2 ≤ r := le_min (by omega) ((Nat.le_div_iff_mul_le wPos).mpr (by omega))
  have fits : r ≤ w := min_le_left _ _
  have wTimes : w*r ≤ budget := (Nat.mul_le_mul_left _ (min_le_right _ _)).trans (Nat.mul_div_le _ _)
  have rowFit : w*r ≤ p := wTimes.trans budgetFit
  have division : budget < w*(budget/w+1) := Nat.lt_mul_div_succ _ wPos
  have toBudget : min budget (w^2) ≤ w*r+w := by
    by_cases complete : w ≤ budget/w
    · have rEq : r = w := min_eq_left complete
      rw [rEq,← Nat.mul_succ,pow_two]
      exact (min_le_right _ _).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
    · have rEq : r = budget/w := min_eq_right (by omega)
      rw [rEq,← Nat.mul_succ]
      exact (min_le_left _ _).trans division.le
  have finiteLower : 2*min p (w^2) ≤ 2*(w*r)+2*w+n+1 := by
    by_cases available : budget ≤ w^2
    · have filled : budget ≤ w*r+w := by simpa only [min_eq_left available] using toBudget
      have row := min_le_left p (w^2)
      omega
    · have filled : w^2 ≤ w*r+w := by simpa only [min_eq_right (le_of_not_ge available)] using toBudget
      have row := min_le_right p (w^2)
      omega
  have degreeUpper : r*n ≤ 4*M := by
    have nWithin : n ≤ 3*w := by omega
    calc
      _ ≤ r*(3*w) := Nat.mul_le_mul_left _ nWithin
      _ = 3*(w*r) := by ring
      _ ≤ 3*p := Nat.mul_le_mul_left _ rowFit
      _ ≤ _ := by omega
  have degreeLower : M ≤ r*(4*n) := by
    refine massUpper.trans ?_
    by_cases complete : w ≤ budget/w
    · have rEq : r = w := min_eq_left complete
      calc
        _ ≤ 4*n*w := rowUpper
        _ = _ := by rw [rEq]; ring
    · have rEq : r = budget/w := min_eq_right (by omega)
      have rounded : budget < w*(r+1) := by rwa [rEq]
      rw [Nat.mul_succ] at rounded
      have enough : 2*w ≤ w*r := by
        rw [Nat.mul_comm 2 w]
        exact Nat.mul_le_mul_left w rLarge
      have row : 2*(w*r) ≤ n*r := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right r nFit
      have nr : 3 ≤ n*r := (show 3 ≤ n by omega).trans (by
        simpa using Nat.mul_le_mul_left n (show 1 ≤ r by omega))
      rw [show r*(4*n) = 4*(n*r) by ring]
      omega
  let _ : NeZero w := ⟨wPos.ne'⟩
  let rows := cyclicPairBandRows fits
  have valid (i : Fin (w*r)) : rows i ≠ [] ∧ (rows i).Nodup := cyclicPairBandRows_valid fits i
  have len (i : Fin (w*r)) : (rows i).length = 2 := rfl
  have free (k : ℕ) : BridgeFree (Before rows) k := cyclicPairBandRows_free fits k
  have unique := nontrivial_halfFree_paths_injective (fun i => (valid i).2) (fun i => by rw [len])
    (by decide : 2 ≤ 2) (free 2).halfFree
  have mass := cyclicPairBandRows_mass fits
  refine ⟨w*r,rowFit,rows,unique,valid,free,mass,finiteLower,?_,?_⟩
  · rw [show (∑ i, (rows i).length) = 2*(w*r) from mass]
    exact (Nat.mul_le_mul_left _ wTimes).trans budgetMass
  · have nPos : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    have pPos : 0 < (p:ℝ) := Nat.cast_pos.mpr (by omega)
    constructor
    · intro x
      rw [show (occurrences (fun i => (rows i).toFinset) x).card = r from cyclicPairBandRows_degree fits x]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
        exact_mod_cast degreeLower
      · apply (le_div_iff₀ nPos).mpr
        exact_mod_cast degreeUpper
    · intro i
      rw [len]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < 4*(p:ℝ))).mpr
        exact_mod_cast (show M ≤ 2*(4*p) by omega)
      · apply (le_div_iff₀ pPos).mpr
        exact_mod_cast (show 2*p ≤ 4*M by omega)

/-- At every cutoff from five onwards, the mass has this uniform
first-order upper bound at an arbitrary row budget. -/
theorem literal_full_mass_le_min_row_or_quarter_square (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n p v q k : ℕ}, N ≤ n → v ≤ n → q ≤ p → 5 ≤ k →
      ∀ rows : Fin q → List (Fin v), Function.Injective rows →
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) → BridgeFree (Before rows) k →
        ((∑ i, (rows i).length : ℕ):ℝ) ≤ 2*min (p:ℝ) ((n:ℝ)^2/4)+ε*(n:ℝ)^2 := by
  obtain ⟨L,long⟩ := full_three_long_mass_subquadratic_within_vertex_budget ε positive
  obtain ⟨U,upper⟩ := literal_full_mass_le_half_square_of_cutoff_five ε positive
  refine ⟨max L U,?_⟩
  intro n p v q k large vFit qFit five rows distinct valid free
  have small := long ((le_max_left L U).trans large) vFit (by omega : 3 ≤ k)
    rows (fun i => (valid i).2) free
  have bound := upper ((le_max_right L U).trans large) vFit five rows distinct valid free
  have pays : ((∑ i, (rows i).length : ℕ):ℝ) ≤ 2*(q:ℝ)+(listMassAboveWidth rows 2:ℝ) := by
    exact_mod_cast list_mass_le_twice_rows_add_long rows
  have qCast : (q:ℝ) ≤ p := by exact_mod_cast qFit
  by_cases bottleneck : (p:ℝ) ≤ (n:ℝ)^2/4
  · rw [min_eq_left bottleneck]
    linarith only [small,pays,qCast]
  · rw [min_eq_right (le_of_not_ge bottleneck)]
    linarith only [bound]

private theorem pairBand_rounding_bound {n p q : ℕ} (nPos : 0 < n)
    (counts : 2*min p ((n/2)^2) ≤ 2*q+2*(n/2)+n+1) :
    2*min (p:ℝ) ((n:ℝ)^2/4) ≤ 2*(q:ℝ)+4*n := by
  let w := n/2
  have twice : (2:ℝ)*w ≤ n := by exact_mod_cast (show 2*w ≤ n by dsimp [w]; omega)
  have near : (n:ℝ) ≤ 2*(w:ℝ)+1 := by exact_mod_cast (show n ≤ 2*w+1 by dsimp [w]; omega)
  have one : (1:ℝ) ≤ n := by exact_mod_cast nPos
  have floorSquare := (sq_le_sq₀ (sub_nonneg.mpr one) (show 0 ≤ (2:ℝ)*w by positivity)).mpr
    (show (n:ℝ)-1 ≤ 2*(w:ℝ) by linarith only [near])
  have round : (n:ℝ)^2/4 ≤ (w:ℝ)^2+(n:ℝ)/2 := by nlinarith only [floorSquare]
  have minRound : min (p:ℝ) ((n:ℝ)^2/4) ≤ min (p:ℝ) ((w:ℝ)^2)+(n:ℝ)/2 := by
    by_cases cap : (p:ℝ) ≤ (w:ℝ)^2
    · rw [min_eq_left cap]
      exact (min_le_left _ _).trans (le_add_of_nonneg_right (by positivity))
    · rw [min_eq_right (le_of_not_ge cap)]
      exact (min_le_right _ _).trans round
  have discrete : 2*min (p:ℝ) ((w:ℝ)^2) ≤ 2*(q:ℝ)+2*(w:ℝ)+n+1 := by
    exact_mod_cast counts
  linarith only [twice,one,minRound,discrete]

private theorem pairBand_row_cap {n p : ℕ} (large : 12 ≤ n)
    (bounds : p ≤ n+2*((n/2)*(n-n/2))) : 3*p ≤ 4*n*(n/2) := by
  let w := n/2
  have wSix : 6 ≤ w := by dsimp [w]; omega
  have nFit : 2*w ≤ n := by dsimp [w]; omega
  have nNear : n ≤ 2*w+1 := by dsimp [w]; omega
  have raw : p ≤ n+2*(w*(w+1)) := bounds.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left w (by omega))) n)
  have cap : (p:ℝ) ≤ n+2*(w:ℝ)*((w:ℝ)+1) := by
    exact_mod_cast (show p ≤ n+2*w*(w+1) by rwa [Nat.mul_assoc])
  have fit : (2:ℝ)*w ≤ n := by exact_mod_cast nFit
  have six : (6:ℝ) ≤ w := by exact_mod_cast wSix
  have pad := mul_nonneg (sub_nonneg.mpr fit) (show 0 ≤ 4*(w:ℝ)-3 by linarith only [six])
  have wCost := mul_nonneg (show 0 ≤ (w:ℝ) by positivity) (sub_nonneg.mpr six)
  exact_mod_cast (show (3:ℝ)*p ≤ 4*(n:ℝ)*w by nlinarith only [cap,pad,wCost])

/-- At any fixed positive quadratic row density, the literal half mass
is `2p` to first order. The optimal literal full mass from cutoff five
is `2 min(p,n²/4)` to first order. A pair witness obtains the lower bound
while keeping both original budgets and all four original-average caps. -/
theorem literal_frozen_full_five_comparison_at_quadratic_path_budget (δ ε : ℝ)
    (δPos : 0 < δ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n p h : ℕ}, N ≤ n → δ*(n:ℝ)^2 ≤ p → 3 ≤ h →
      ∀ paths : Fin p → List (Fin n), Function.Injective paths →
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) → HalfBridgeFree (Before paths) h →
        let M := ∑ i, (paths i).length
        (2*(p:ℝ)-ε*(n:ℝ)^2 ≤ (M:ℝ) ∧ (M:ℝ) ≤ 2*(p:ℝ)+ε*(n:ℝ)^2) ∧
        (∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
          (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ (∀ k, BridgeFree (Before rows) k) ∧
          2*min (p:ℝ) ((n:ℝ)^2/4)-ε*(n:ℝ)^2 ≤ ((∑ i, (rows i).length : ℕ):ℝ) ∧
          (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows) ∧
        ∀ {v q k : ℕ}, v ≤ n → q ≤ p → 5 ≤ k → ∀ rows : Fin q → List (Fin v), Function.Injective rows →
          (∀ i, rows i ≠ [] ∧ (rows i).Nodup) → BridgeFree (Before rows) k →
          ((∑ i, (rows i).length : ℕ):ℝ) ≤ 2*min (p:ℝ) ((n:ℝ)^2/4)+ε*(n:ℝ)^2 := by
  let η := min ε δ
  obtain ⟨C,halfMass⟩ := half_three_mass_le_twice_paths_add_subquadratic η (lt_min positive δPos)
  obtain ⟨U,fullMass⟩ := literal_full_mass_le_min_row_or_quarter_square ε positive
  let densityThreshold := ⌈3/δ⌉₊
  let errorThreshold := ⌈4/ε⌉₊
  let N := max 12 (max densityThreshold (max errorThreshold (max C U)))
  refine ⟨N,?_⟩
  intro n p h large dense three paths distinct valid half
  let M : ℕ := ∑ i, (paths i).length
  have nLarge : 12 ≤ n := by dsimp [N] at large; omega
  have smallThreshold : densityThreshold ≤ n := by dsimp [N] at large; omega
  have largeThreshold : errorThreshold ≤ n := by dsimp [N] at large; omega
  have CEnough : C ≤ n := by dsimp [N] at large; omega
  have UEnough : U ≤ n := by dsimp [N] at large; omega
  have densityGate : (3:ℝ)/δ ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.mpr smallThreshold)
  have errorGate : (4:ℝ)/ε ≤ n := (Nat.le_ceil _).trans (Nat.cast_le.mpr largeThreshold)
  have rowLower : 3*n ≤ p := by
    have ready := mul_le_mul_of_nonneg_right ((div_le_iff₀ δPos).mp densityGate)
      (show 0 ≤ (n:ℝ) by positivity)
    exact_mod_cast (show (3:ℝ)*n ≤ p by nlinarith only [ready,dense])
  have errorFits : (4:ℝ)*n ≤ ε*(n:ℝ)^2 := by
    have ready := mul_le_mul_of_nonneg_right ((div_le_iff₀ positive).mp errorGate)
      (show 0 ≤ (n:ℝ) by positivity)
    nlinarith only [ready]
  have rowUpper := pairBand_row_cap nLarge (literal_half_path_count_le_balanced_bipartite distinct valid half three)
  have massLower : 2*p ≤ M+n := by
    have pathCount := literal_path_count_le_vertices_add_gaps distinct (fun i => (valid i).1)
    have link := rowMass_eq_gaps_add_count (fun i => (valid i).1)
    rw [Fintype.card_fin] at link
    dsimp only [M]
    omega
  have near : (M:ℝ) ≤ 2*(p:ℝ)+η*(n:ℝ)^2 := halfMass CEnough three paths (fun i => (valid i).2) half
  have useDensity := mul_le_mul_of_nonneg_right (min_le_right ε δ) (sq_nonneg (n:ℝ))
  have massUpper : M ≤ 3*p := by exact_mod_cast (show (M:ℝ) ≤ 3*(p:ℝ) by linarith only [near,useDensity,dense])
  obtain ⟨q,qFit,rows,rowsDistinct,rowsValid,rowsFree,exactMass,round,within,caps⟩ :=
    frozen_full_cyclic_band_of_row_budget (by omega : 6 ≤ n) rowLower rowUpper massLower massUpper
  have compare := pairBand_rounding_bound (by omega : 0 < n) round
  have halfLower : (2:ℝ)*p ≤ (M:ℝ)+n := by exact_mod_cast massLower
  have useError := mul_le_mul_of_nonneg_right (min_le_left ε δ) (sq_nonneg (n:ℝ))
  refine ⟨⟨?_,?_⟩,⟨2*(n/2),by omega,q,qFit,rows,rowsDistinct,rowsValid,rowsFree,?_,within,caps⟩,?_⟩
  · linarith only [errorFits,halfLower,show (0:ℝ) ≤ n by positivity]
  · linarith only [near,useError]
  · rw [exactMass,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [compare,errorFits]
  · exact fullMass UEnough

end OnlineReachabilityPreservers
