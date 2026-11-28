import OnlineReachabilityPreservers.AllSizeLiteralFeasibility
import OnlineReachabilityPreservers.DistinctPathBudgets
import OnlineReachabilityPreservers.FullThreeFrozenMassAudit
import OnlineReachabilityPreservers.HalfAllLiteralCapacity

/-! Sharp mass comparison at the saturated half budget and a full cutoff covering the vertices. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- When the full cutoff covers either of a literal witness’s budgets,
its mass is at most half the original vertex square plus an arbitrarily
small quadratic error. -/
theorem literal_full_mass_le_half_square_of_cutoff_covers_support (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n v q k : ℕ}, N ≤ n → v ≤ n → min v q ≤ k → ∀ rows : Fin q → List (Fin v),
      Function.Injective rows → (∀ i, rows i ≠ [] ∧ (rows i).Nodup) →
      BridgeFree (Before rows) k →
      ((∑ i, (rows i).length : ℕ):ℝ) ≤ (1/2+ε)*(n:ℝ)^2 := by
  obtain ⟨N,small⟩ := full_three_long_mass_subquadratic_within_vertex_budget (ε/2) (by positivity)
  refine ⟨max N (max 8 ⌈4/ε⌉₊),?_⟩
  intro n v q k large fits covers rows distinct valid full
  have nEight : 8 ≤ n := le_trans (le_max_left _ _) ((le_max_right N _).trans large)
  have enough : (4:ℝ)/ε ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_trans (le_max_right 8 _) ((le_max_right N _).trans large)))
  have all := bridgeFree_all_of_cutoff_ge_min full covers
  have bound := literal_full_all_path_count_le_tree_or_bipartite rows distinct valid all
  have smallStar : 2*(v-1) ≤ n^2/4 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    calc
      (2*(v-1))*4 ≤ (2*n)*4 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans fits))
      _ = 8*n := by ring
      _ ≤ n^2 := by rw [pow_two]; exact Nat.mul_le_mul_right n nEight
  have smallPairs : v^2/4 ≤ n^2/4 :=
    Nat.div_le_div_right (Nat.pow_le_pow_left fits 2)
  have cap : q ≤ n+n^2/4 := bound.trans (Nat.add_le_add fits (max_le smallStar smallPairs))
  have floorCast : (4:ℝ)*((n^2/4 : ℕ):ℝ) ≤ (n:ℝ)^2 := by
    exact_mod_cast (show 4*(n^2/4) ≤ n^2 by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
  have capCast : (q:ℝ) ≤ ((n+n^2/4:ℕ):ℝ) := by exact_mod_cast cap
  rw [Nat.cast_add] at capCast
  have qCap : (q:ℝ) ≤ n+(n:ℝ)^2/4 := by linarith only [floorCast,capCast]
  have mass : (∑ i, (rows i).length) ≤ 2*q+listMassAboveWidth rows 2 := calc
    _ ≤ ∑ i, (2+(if 2 < (rows i).length then (rows i).length else 0)) := by
      apply sum_le_sum
      intro i _
      by_cases long : 2 < (rows i).length
      · simp [long]
      · simpa [long] using (le_of_not_gt long)
    _ = _ := by rw [sum_add_distrib, show (∑ _ : Fin q, (2:ℕ)) = 2*q by simp [Nat.mul_comm]]
                simp [listMassAboveWidth,sum_filter]
  have long := small ((le_max_left N _).trans large) fits (le_rfl : 3 ≤ 3) rows (fun i => (valid i).2) (fun d _ => all d)
  have realMass : ((∑ i, (rows i).length : ℕ):ℝ) ≤ 2*(q:ℝ)+(listMassAboveWidth rows 2:ℝ) := by
    exact_mod_cast mass
  have epsN : (4:ℝ) ≤ (n:ℝ)*ε := (div_le_iff₀ positive).mp enough
  have absorb := mul_le_mul_of_nonneg_right epsN (show 0 ≤ (n:ℝ) by positivity)
  nlinarith only [qCap,long,realMass,absorb]
/-- Twice the number of unordered distinct pairs plus the singletons is the vertex square. -/
theorem twice_choose_two_add_self (n : ℕ) : 2*n.choose 2+n = n^2 := by
  rw [Nat.choose_two_right,Nat.mul_div_cancel' n.even_mul_pred_self.two_dvd,Nat.mul_sub_left_distrib,mul_one,pow_two]
  exact Nat.sub_add_cancel (Nat.le_mul_self _)

/-- Uniform one-way pair rows meet all four original caps at the
saturated half budget. Their mass is at least half the vertex square
minus an arbitrarily small quadratic error. -/
theorem frozen_full_all_pairs_at_saturated_half_budget (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n →
      let p := n+n.choose 2+1
      let M := n^2+2
      ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ (∀ k, BridgeFree (Before rows) k) ∧
        (1/2-ε)*(n:ℝ)^2 ≤ ((∑ i, (rows i).length : ℕ):ℝ) ∧
        (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  refine ⟨max 3 ⌈1/ε⌉₊,?_⟩
  intro n large
  let p := n+n.choose 2+1
  let M := n^2+2
  let m := n/2
  let rows := frozenRectangleRows 1 m
  have nLarge : 3 ≤ n := (le_max_left _ _).trans large
  have vFit : 2*m ≤ n := by dsimp [m]; omega
  have vNear : n ≤ 2*m+1 := by dsimp [m]; omega
  have cap : n+1 ≤ 4*m := by omega
  have model : 2*p = M+n := by
    dsimp [p,M]
    have model := twice_choose_two_add_self n
    omega
  have qFit : m*m ≤ p := by
    have squared := Nat.pow_le_pow_left vFit 2
    have transform : (2*m)^2 = 4*(m*m) := by ring
    rw [transform] at squared
    dsimp [M] at model
    omega
  have len (i : Fin (1*(m*m))) : (rows i).length = 2 := rfl
  have mass : (∑ i, (rows i).length) = 2*(m*m) := by simp [len,Nat.mul_comm]
  have free : ∀ cutoff, BridgeFree (Before rows) cutoff := frozenRectangleRows_free 1 m
  have simple (i : Fin (1*(m*m))) : (rows i).Nodup := frozenRectangleRows_simple i
  have distinct := nontrivial_halfFree_paths_injective simple (fun i => by rw [len]) (by decide : 2 ≤ 2)
    (free 2).halfFree
  refine ⟨1*(2*m),by simpa only [one_mul] using vFit,1*(m*m),by simpa only [one_mul] using qFit,
    rows,distinct,fun i => ⟨by simp [rows,frozenRectangleRows],simple i⟩,free,?_,?_,?_⟩
  · have size : (1:ℝ)/ε ≤ n :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right 3 _).trans large))
    have epsN : (1:ℝ) ≤ (n:ℝ)*ε := (div_le_iff₀ positive).mp size
    have abs := mul_le_mul_of_nonneg_right epsN (show 0 ≤ (n:ℝ) by positivity)
    have near : (n:ℝ) ≤ 2*(m:ℝ)+1 := by exact_mod_cast vNear
    have nReal : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have squared := (sq_le_sq₀ (sub_nonneg.mpr nReal)
      (show 0 ≤ 2*(m:ℝ) by positivity)).mpr (show (n:ℝ)-1 ≤ 2*(m:ℝ) by linarith only [near])
    rw [mass]
    push_cast
    nlinarith only [squared,abs]
  · rw [mass]
    have squared := Nat.pow_le_pow_left vFit 2
    have transform : (2*m)^2 = 4*(m*m) := by ring
    rw [transform] at squared
    omega
  · constructor
    · intro x
      rw [frozenRectangleRows_degree]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
        have raw : M ≤ m*(4*n) := calc
          _ ≤ n^2+n := by dsimp [M]; omega
          _ = (n+1)*n := by ring
          _ ≤ (4*m)*n := Nat.mul_le_mul_right n cap
          _ = _ := by ring
        exact_mod_cast raw
      · apply (le_div_iff₀ (by positivity : (0:ℝ) < n)).mpr
        have raw : m*n ≤ n^2 := by rw [pow_two]; exact Nat.mul_le_mul_right n (by omega)
        exact_mod_cast raw.trans (show n^2 ≤ 4*M by dsimp [M]; omega)
    · intro i
      rw [len]
      have pPos : 0 < p := by dsimp [p]; omega
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < 4*(p:ℝ))).mpr
        exact_mod_cast (show M ≤ 2*(4*p) by omega)
      · apply (le_div_iff₀ (by positivity : (0:ℝ) < p)).mpr
        have nSmall : n ≤ M := by
          have product := Nat.le_mul_self n
          dsimp [M]
          rw [pow_two]
          omega
        exact_mod_cast (show 2*p ≤ 4*M by omega)

/-- At the saturated literal half budget the half mass is exactly
(n^2+2), and the full mass is asymptotically half the vertex square
when the cutoff covers the smaller support. A single full witness
achieves the lower bound and all four starting-average caps. -/
theorem literal_saturated_half_full_mass_comparison (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n →
      let p := n+n.choose 2+1
      let M := n^2+2
      (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ (∀ k, HalfBridgeFree (Before paths) k) ∧
        (∑ i, (paths i).length) = M) ∧
      (∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ (∀ k, BridgeFree (Before rows) k) ∧
        (1/2-ε)*(n:ℝ)^2 ≤ ((∑ i, (rows i).length : ℕ):ℝ) ∧
        (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows) ∧
      ∀ {v q k : ℕ}, v ≤ n → q ≤ p → min v q ≤ k → ∀ rows : Fin q → List (Fin v),
        Function.Injective rows → (∀ i, rows i ≠ [] ∧ (rows i).Nodup) →
        BridgeFree (Before rows) k →
        ((∑ i, (rows i).length : ℕ):ℝ) ≤ (1/2+ε)*(n:ℝ)^2 := by
  obtain ⟨U,upper⟩ := literal_full_mass_le_half_square_of_cutoff_covers_support ε positive
  obtain ⟨L,lower⟩ := frozen_full_all_pairs_at_saturated_half_budget ε positive
  refine ⟨max (max U L) 2,?_⟩
  intro n large
  let p := n+n.choose 2+1
  have atLeastTwo : 2 ≤ n := (le_max_right _ _).trans large
  have enough : max U L ≤ n := (le_max_left _ _).trans large
  obtain ⟨paths,distinct,valid,all⟩ := literal_half_all_of_choose_budget (n := n) (p := p)
    (by simp [p,atLeastTwo])
  have exactMass := literal_half_mass_at_saturated_four_budget distinct valid (all 4) le_rfl
  have identity := twice_choose_two_add_self n
  refine ⟨⟨paths,distinct,valid,all,by omega⟩,lower ((le_max_right U L).trans enough),?_⟩
  intro v q k vFit _ cutoff rows unique well full
  exact upper ((le_max_left U L).trans enough) vFit cutoff rows unique well full

end OnlineReachabilityPreservers
