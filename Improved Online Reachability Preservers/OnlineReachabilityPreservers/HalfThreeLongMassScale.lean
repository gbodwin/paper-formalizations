import OnlineReachabilityPreservers.PositiveMatchingDensity

/-! The half-three long-row mass is small at the `n √p` scale. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- For sufficiently large row budgets, the long-row mass of a simple
half-three-free family is at most any prescribed fraction of `n √p`.
The threshold is independent of the vertex budget and the cutoff. -/
theorem half_three_long_mass_small_n_sqrt_p (η : ℝ) (ηPos : 0 < η) :
    ∃ P : ℕ, ∀ {n p k : ℕ}, P ≤ p → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) k →
      (listMassAboveWidth paths 2:ℝ) ≤ η*(n:ℝ)*Real.sqrt p := by
  obtain ⟨δ,δPos,P,_,density⟩ := half_three_n_sqrt_p_mass_requires_quadratic_path_density η ηPos
  obtain ⟨N,small⟩ := half_three_mass_le_twice_paths_add_subquadratic (δ/2) (by positivity)
  let R := max P (N^2)
  refine ⟨⌈((R:ℝ)/η)^2⌉₊+1,?_⟩
  intro n p cutoff large three paths simple free
  let long := (univ : Finset (Fin p)).filter fun i => 2 < (paths i).length
  let enumerate := Fintype.orderIsoFinOfCardEq (↥long) (Fintype.card_coe long)
  let parent (i : Fin long.card) : Fin p := (enumerate i).val
  let kept (i : Fin long.card) := paths (parent i)
  let M := ∑ i, (kept i).length
  have count : long.card ≤ p := by simpa only [card_univ,Fintype.card_fin] using card_le_univ long
  have mass : M = listMassAboveWidth paths 2 :=
    (Equiv.sum_comp enumerate.toEquiv (fun i : long => (paths i.val).length)).trans
      (long.sum_coe_sort (fun i => (paths i).length))
  have keptSimple (i : Fin long.card) : (kept i).Nodup := simple (parent i)
  have keptFree : HalfBridgeFree (Before kept) cutoff := by
    intro d fits bridge earlier
    have injective : Function.Injective parent := Subtype.val_injective.comp enumerate.injective
    exact free fits (bridge.mapPaths parent injective (fun _ _ _ step => step)) (enumerate.strictMono earlier)
  have lengthLeast : 3*long.card ≤ M := calc
    _ = ∑ _i : Fin long.card, (3:ℕ) := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum fun i _ => (mem_filter.mp (enumerate i).property).2
  have lengthMost : M ≤ n*long.card := calc
    _ ≤ ∑ _i : Fin long.card, n := sum_le_sum fun i _ => by
      rw [← List.toFinset_card_of_nodup (keptSimple i)]
      simpa only [card_univ,Fintype.card_fin] using card_le_univ (kept i).toFinset
    _ = _ := by simp [Nat.mul_comm]
  rw [← mass]
  by_contra! big
  have nPos : 0 < n := by
    by_contra! zero
    have empty : n = 0 := by omega
    simp [empty] at lengthMost big
    omega
  have nPositive : (0:ℝ) < n := Nat.cast_pos.mpr nPos
  have cap : (M:ℝ) ≤ (n:ℝ)*(long.card:ℝ) := by exact_mod_cast lengthMost
  have many : η*Real.sqrt p ≤ (long.card:ℝ) := by
    apply (mul_le_mul_iff_right₀ nPositive).mp
    calc
      _ = η*(n:ℝ)*Real.sqrt p := by ring
      _ ≤ M := big.le
      _ ≤ _ := by simpa [mul_comm] using cap
  have threshold : ((R:ℝ)/η)^2 ≤ (p:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
  have root : (R:ℝ)/η ≤ Real.sqrt p := by
    refine (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp ?_
    rwa [Real.sq_sqrt (Nat.cast_nonneg _)]
  have plenty : R ≤ long.card := by
    have fits := (div_le_iff₀ ηPos).mp root
    have real : (R:ℝ) ≤ (long.card:ℝ) := fits.trans (by simpa [mul_comm] using many)
    exact_mod_cast real
  have underSquare : long.card ≤ n^2 := by
    have pairs := listMass_le_ordered_pairs_add_paths kept keptSimple keptFree (by omega)
    have nCap := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    rw [pow_two]
    omega
  have nLarge : N ≤ n := by
    by_contra! under
    exact (Nat.pow_lt_pow_left under (by decide : 2 ≠ 0)).not_ge
      (((le_max_right P (N^2)).trans plenty).trans underSquare)
  have enoughRows : P ≤ long.card := (le_max_left P _).trans plenty
  have pScale : Real.sqrt (long.card:ℝ) ≤ Real.sqrt (p:ℝ) := Real.sqrt_le_sqrt (Nat.cast_le.mpr count)
  have largeKept : η*(n:ℝ)*Real.sqrt long.card ≤ (M:ℝ) :=
    (mul_le_mul_of_nonneg_left pScale (by positivity)).trans big.le
  have pathDense := density nPos enoughRows three kept keptSimple keptFree largeKept
  have smallKept := small nLarge three kept keptSimple keptFree
  have atLeast : (3:ℝ)*(long.card:ℝ) ≤ (M:ℝ) := by exact_mod_cast lengthLeast
  nlinarith only [pathDense,smallKept,atLeast,mul_pos δPos (sq_pos_of_pos nPositive)]

/-- The same estimate holds at every size with an additive term linear
in the vertex budget. Its constant depends only on the chosen error. -/
theorem half_three_long_mass_le_small_n_sqrt_p_add_linear (η : ℝ) (ηPos : 0 < η) :
    ∃ C : ℕ, ∀ {n p k : ℕ}, 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) k →
      (listMassAboveWidth paths 2:ℝ) ≤ η*(n:ℝ)*Real.sqrt p+(C:ℝ)*n := by
  obtain ⟨P,small⟩ := half_three_long_mass_small_n_sqrt_p η ηPos
  refine ⟨P,?_⟩
  intro n p k three paths simple free
  by_cases large : P ≤ p
  · exact (small large three paths simple free).trans (le_add_of_nonneg_right (by positivity))
  have bound : listMassAboveWidth paths 2 ≤ P*n := calc
    _ ≤ ∑ i, (paths i).length := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ ∑ _i : Fin p, n := sum_le_sum fun i _ => by
      rw [← List.toFinset_card_of_nodup (simple i)]
      simpa only [card_univ,Fintype.card_fin] using card_le_univ (paths i).toFinset
    _ = p*n := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (le_of_not_ge large)
  exact (show (listMassAboveWidth paths 2:ℝ) ≤ (P:ℝ)*n by exact_mod_cast bound).trans
    (le_add_of_nonneg_left (by positivity))

/-- The estimate also holds uniformly over smaller output budgets. -/
theorem half_three_long_mass_small_n_sqrt_p_within_budgets (η : ℝ) (ηPos : 0 < η) :
    ∃ P : ℕ, 0 < P ∧ ∀ {n p v q k : ℕ}, P ≤ p → v ≤ n → q ≤ p → 3 ≤ k →
      ∀ paths : Fin q → List (Fin v), (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) k →
      (listMassAboveWidth paths 2:ℝ) ≤ η*(n:ℝ)*Real.sqrt p := by
  let ε := η/2
  have εPos : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,uniform⟩ := half_three_long_mass_le_small_n_sqrt_p_add_linear ε εPos
  refine ⟨⌈((C:ℝ)/ε)^2⌉₊+1,by positivity,?_⟩
  intro n p v q k large vFits qFits three paths simple free
  have number : ((C:ℝ)/ε)^2 ≤ (p:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
  have root : (C:ℝ)/ε ≤ Real.sqrt p := by
    refine (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp ?_
    rwa [Real.sq_sqrt (Nat.cast_nonneg _)]
  have linear : (C:ℝ) ≤ ε*Real.sqrt p := by
    simpa only [mul_comm] using (div_le_iff₀ εPos).mp root
  have nFits : (v:ℝ) ≤ n := Nat.cast_le.mpr vFits
  have pFits : Real.sqrt q ≤ Real.sqrt p := Real.sqrt_le_sqrt (Nat.cast_le.mpr qFits)
  calc
    _ ≤ ε*(v:ℝ)*Real.sqrt q+(C:ℝ)*v := uniform three paths simple free
    _ ≤ ε*(n:ℝ)*Real.sqrt p+(C:ℝ)*n := by gcongr
    _ ≤ ε*(n:ℝ)*Real.sqrt p+(ε*Real.sqrt p)*(n:ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right linear (Nat.cast_nonneg _))
    _ = _ := by dsimp [ε]; ring

/-- Adding the short rows gives the corresponding bound on total mass. -/
theorem half_three_mass_le_twice_paths_add_small_n_sqrt_p (η : ℝ) (ηPos : 0 < η) :
    ∃ P : ℕ, ∀ {n p k : ℕ}, P ≤ p → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) k →
      ((∑ i, (paths i).length : ℕ):ℝ) ≤ 2*(p:ℝ)+η*(n:ℝ)*Real.sqrt p := by
  obtain ⟨P,small⟩ := half_three_long_mass_small_n_sqrt_p η ηPos
  refine ⟨P,?_⟩
  intro n p k large three paths simple free
  have split : ((∑ i, (paths i).length : ℕ):ℝ) ≤ 2*(p:ℝ)+(listMassAboveWidth paths 2:ℝ) := by
    exact_mod_cast mass_le_twice_paths_add_long_mass paths
  linarith only [split,small large three paths simple free]

end OnlineReachabilityPreservers
