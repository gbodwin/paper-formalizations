import OnlineReachabilityPreservers.LocalOfflineBound
import OnlineReachabilityPreservers.OfflineLatticeLower

/-! Partial bounds for the extremal lower direction of Lemma 14. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem offlineRate_le_sparse {b n p R : ℝ} (hb : 2/3 ≤ b) (hb' : b ≤ 1)
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hR : 1 ≤ R) (sparse : p^2 ≤ R*n) :
    offlineRate b n p ≤ R*n := by
  have n0 : 0 ≤ n := zero_le_one.trans hn
  have p0 : 0 ≤ p := zero_le_one.trans hp
  have R0 : 0 ≤ R := zero_le_one.trans hR
  have pRoot : p ≤ (R*n)^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt p0 (mul_nonneg R0 n0)).mpr sparse
  have nBound : n ≤ R*n := le_mul_of_one_le_left n0 hR
  have pBound : p ≤ R*n := (le_mul_of_one_le_left p0 hp).trans (by simpa [pow_two] using sparse)
  have first : n^(3/4 : ℝ)*p^(1/2 : ℝ) ≤ R*n := calc
    _ ≤ n^(3/4 : ℝ)*((R*n)^(1/2 : ℝ))^(1/2 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow p0 pRoot (by norm_num)) (by positivity)
    _ = R^(1/4 : ℝ)*n := by
      rw [← Real.rpow_mul (mul_nonneg R0 n0), show (1/2 : ℝ)*(1/2) = 1/4 by norm_num,
        Real.mul_rpow R0 n0, mul_left_comm, ← Real.rpow_add (by linarith : 0 < n),
        show (3/4 : ℝ)+1/4 = 1 by norm_num, Real.rpow_one]
    _ ≤ R*n := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le hR (by norm_num)) n0
  have second : n^(2-2*b)*p^b ≤ R*n := calc
    _ ≤ n^(2-2*b)*((R*n)^(1/2 : ℝ))^b :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow p0 pRoot (by linarith)) (by positivity)
    _ = R^(b/2)*n^(2-3*b/2) := by
      rw [← Real.rpow_mul (mul_nonneg R0 n0), show (1/2 : ℝ)*b = b/2 by ring,
        Real.mul_rpow R0 n0, mul_left_comm, ← Real.rpow_add (by linarith : 0 < n)]
      ring_nf
    _ ≤ R*n := mul_le_mul (Real.rpow_le_self_of_one_le hR (by linarith))
      (Real.rpow_le_self_of_one_le hn (by linarith)) (by positivity) R0
  exact max_le nBound (max_le first (max_le second pBound))

private theorem offlineRate_le_dense {b n p R : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1)
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hR : 1 ≤ R) (dense : n^2 ≤ R*p) :
    offlineRate b n p ≤ R*p := by
  have n0 : 0 ≤ n := zero_le_one.trans hn
  have p0 : 0 ≤ p := zero_le_one.trans hp
  have R0 : 0 ≤ R := zero_le_one.trans hR
  have nBound : n ≤ R*p := (le_mul_of_one_le_left n0 hn).trans (by simpa [pow_two] using dense)
  have pBound : p ≤ R*p := le_mul_of_one_le_left p0 hR
  have compare (a : ℝ) (ha : 0 ≤ a) : (n^2)^a ≤ (R*p)^a :=
    Real.rpow_le_rpow (sq_nonneg _) dense ha
  have first : n^(3/4 : ℝ)*p^(1/2 : ℝ) ≤ R*p := calc
    _ = (n^2)^(3/8 : ℝ)*p^(1/2 : ℝ) := by
      rw [← Real.rpow_natCast_mul n0]
      norm_num
    _ ≤ (R*p)^(3/8 : ℝ)*p^(1/2 : ℝ) :=
      mul_le_mul_of_nonneg_right (compare _ (by norm_num)) (by positivity)
    _ = R^(3/8 : ℝ)*p^(7/8 : ℝ) := by
      rw [Real.mul_rpow R0 p0, mul_assoc, ← Real.rpow_add (by linarith : 0 < p)]
      norm_num
    _ ≤ R*p := mul_le_mul (Real.rpow_le_self_of_one_le hR (by norm_num))
      (Real.rpow_le_self_of_one_le hp (by norm_num)) (by positivity) R0
  have second : n^(2-2*b)*p^b ≤ R*p := calc
    _ = (n^2)^(1-b)*p^b := by
      rw [← Real.rpow_natCast_mul n0]
      congr 2
      push_cast
      ring
    _ ≤ (R*p)^(1-b)*p^b :=
      mul_le_mul_of_nonneg_right (compare _ (by linarith)) (by positivity)
    _ = R^(1-b)*p := by
      rw [Real.mul_rpow R0 p0, mul_assoc, ← Real.rpow_add (by linarith : 0 < p),
        sub_add_cancel, Real.rpow_one]
    _ ≤ R*p := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le hR (by linarith)) p0
  exact max_le nBound (max_le first (max_le second pBound))

/-- In the sparse and dense linear regimes, the offline extremal construction
dominates the mass of every simple path family with no bridge through size
four. The graph and its exact-size demand set are uniform over the families. -/
theorem theorem14_extremal_lower_in_linear_regimes :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {n p K : ℕ}, 2 ≤ n → 0 < p → p ≤ n^2 → 1 ≤ K →
      (p^2 ≤ K*n ∨ n^2 ≤ K*p) →
      ∃ (G : Arcs (Fin n)) (D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
        ∀ H ⊆ G, Preserves G H D.toList →
          ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) →
            BridgeFree (ListBefore paths) 4 →
            (∑ i, ((paths i).length : ℝ)) ≤ C*K*H.card := by
  obtain ⟨B, hB, bound⟩ := theorem43_list_limit.{0}
  refine ⟨6*B, by linarith, ?_⟩
  intro n p K hn hp hpCap hK regimes
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have bSq : (1/Real.sqrt 2)^2 = (1/2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have bLow : (2/3 : ℝ) ≤ 1/Real.sqrt 2 := by
    apply (sq_le_sq₀ (by norm_num) (by positivity)).mp
    rw [bSq]
    norm_num
  have bHigh : (1/Real.sqrt 2 : ℝ) ≤ 1 := offline_limit_lt.le.trans (by norm_num)
  have incidence (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
      (free : BridgeFree (ListBefore paths) 4) :
      (∑ i, ((paths i).length : ℝ)) ≤ offlineRate (1/Real.sqrt 2) n p * B := by
    simpa using bound (Fin n) p paths simple free
  rcases regimes with sparse | dense
  · obtain ⟨G, D, dag, size, lower⟩ := offline_linear_vertex_lower hn hp hpCap
    have rate := offlineRate_le_sparse bLow bHigh hn' hp' hK' (by exact_mod_cast sparse)
    refine ⟨G, D, dag, size, ?_⟩
    intro H sub preserves paths simple free
    have edgeCount : (n : ℝ) ≤ 6*H.card := by
      have edges := lower H sub preserves
      exact_mod_cast (show n ≤ 6*H.card by omega)
    calc
      _ ≤ offlineRate (1/Real.sqrt 2) n p * B := incidence paths simple free
      _ ≤ (K*n)*B := mul_le_mul_of_nonneg_right rate (by linarith)
      _ ≤ (K*(6*H.card))*B := by gcongr
      _ = _ := by ring
  · obtain ⟨G, D, dag, size, lower⟩ := offline_linear_demand_lower hn hpCap
    have rate := offlineRate_le_dense (by positivity : 0 ≤ 1/Real.sqrt 2) bHigh hn' hp' hK'
      (by exact_mod_cast dense)
    refine ⟨G, D, dag, size, ?_⟩
    intro H sub preserves paths simple free
    have edgeCount : (p : ℝ) ≤ 6*H.card := by exact_mod_cast lower H sub preserves
    calc
      _ ≤ offlineRate (1/Real.sqrt 2) n p * B := incidence paths simple free
      _ ≤ (K*p)*B := mul_le_mul_of_nonneg_right rate (by linarith)
      _ ≤ (K*(6*H.card))*B := by gcongr
      _ = _ := by ring

private theorem offlineRate_le_three_lattice_gap {b n p : ℝ} (bLo : 2/3 ≤ b) (bHi : b ≤ 3/4)
    (hn : 1 ≤ n) (hp : 1 ≤ p) :
    offlineRate b n p ≤ n^((7-8*b)/10) * (n + p + n^(2/3 : ℝ)*p^(1/2 : ℝ) + n^(1/2 : ℝ)*p^(2/3 : ℝ) +
      n^(2/5 : ℝ)*p^(3/4 : ℝ)) := by
  let d := (7-8*b)/10
  let firstLattice := n^(2/3 : ℝ)*p^(1/2 : ℝ)
  let secondLattice := n^(1/2 : ℝ)*p^(2/3 : ℝ)
  let thirdLattice := n^(2/5 : ℝ)*p^(3/4 : ℝ)
  let base := n + p + firstLattice + secondLattice + thirdLattice
  have nPos : 0 < n := by linarith
  have pPos : 0 < p := by linarith
  have dLo : (1/12 : ℝ) ≤ d := by dsimp [d]; linarith
  have d0 : 0 ≤ d := by linarith
  have size : 1 ≤ n^d := Real.one_le_rpow hn d0
  have first0 : 0 ≤ firstLattice := by dsimp [firstLattice]; positivity
  have second0 : 0 ≤ secondLattice := by dsimp [secondLattice]; positivity
  have third0 : 0 ≤ thirdLattice := by dsimp [thirdLattice]; positivity
  have nLe : n ≤ base := by dsimp [base]; linarith only [pPos, first0, second0, third0]
  have pLe : p ≤ base := by dsimp [base]; linarith only [nPos, first0, second0, third0]
  have firstLe : firstLattice ≤ base := by dsimp [base]; linarith only [nPos, pPos, second0, third0]
  have secondLe : secondLattice ≤ base := by dsimp [base]; linarith only [nPos, pPos, first0, third0]
  have thirdLe : thirdLattice ≤ base := by dsimp [base]; linarith only [nPos, pPos, first0, second0]
  have baseLe : base ≤ n^d*base := le_mul_of_one_le_left (by positivity) size
  have first : n^(3/4 : ℝ)*p^(1/2 : ℝ) ≤ n^d * base := calc
    _ = n^(1/12 : ℝ)*(n^(2/3 : ℝ)*p^(1/2 : ℝ)) := by
      rw [← mul_assoc, ← Real.rpow_add nPos]
      norm_num
    _ ≤ n^d * base := mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn dLo) firstLe first0 (by positivity)
  have mixed : n^(2-2*b)*p^b ≤ n^d*base := by
    by_cases below : p ≤ n^(6/5 : ℝ)
    · calc
        _ = n^(2-2*b)*p^(b-2/3)*p^(2/3 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add pPos, sub_add_cancel]
        _ ≤ n^(2-2*b)*(n^(6/5 : ℝ))^(b-2/3)*p^(2/3 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow pPos.le below (by linarith)) (by positivity)
        _ = n^d*secondLattice := by
          dsimp only [secondLattice]
          rw [← Real.rpow_mul nPos.le, ← Real.rpow_add nPos, ← mul_assoc, ← Real.rpow_add nPos]
          congr 2
          dsimp [d]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left secondLe (by positivity)
    · calc
        _ = n^(2-2*b)*p^(b-3/4)*p^(3/4 : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add pPos, sub_add_cancel]
        _ ≤ n^(2-2*b)*(n^(6/5 : ℝ))^(b-3/4)*p^(3/4 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_not_ge below)
            (by linarith)) (by positivity)
        _ = n^d*thirdLattice := by
          dsimp only [thirdLattice]
          rw [← Real.rpow_mul nPos.le, ← Real.rpow_add nPos, ← mul_assoc, ← Real.rpow_add nPos]
          congr 2
          dsimp [d]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left thirdLe (by positivity)
  exact max_le (nLe.trans baseLe) (max_le first (max_le mixed (pLe.trans baseLe)))

/-- At every admissible parameter pair, the three lattice rates give a
preserver lower bound within a factor `C*n^((7-8/sqrt 2)/10)` of the mass of
every simple system excluding full bridges through four. -/
theorem theorem14_extremal_lower_with_three_lattice_gap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {n p : ℕ}, 2 ≤ n → 0 < p → p ≤ n^2 →
      ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
        ∀ H ⊆ G, Preserves G H D.toList →
          ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) →
            BridgeFree (ListBefore paths) 4 →
            (∑ i, ((paths i).length : ℝ)) ≤
              C*(n : ℝ)^((7-8*(1/Real.sqrt 2))/10)*H.card := by
  obtain ⟨B, hB, bound⟩ := theorem43_list_limit.{0}
  refine ⟨4718592*B, by linarith, ?_⟩
  intro n p hn hp hpCap
  obtain ⟨G,D,dag,size,lower⟩ := SourceAudit.offline_lower_all_sizes_with_three_lattices hn hp hpCap
  refine ⟨G,D,dag,size,?_⟩
  intro H sub preserves paths simple free
  let b := 1/Real.sqrt 2
  have bn : (2/3 : ℝ) ≤ b := by
    have sq : b^2 = (1/2 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    exact (sq_le_sq₀ (by norm_num) (by positivity)).mp (by linarith)
  have bh : b ≤ (3/4 : ℝ) := offline_limit_lt.le.trans (by norm_num)
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have p1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have incidence : (∑ i, ((paths i).length : ℝ)) ≤ offlineRate b n p * B := by
    simpa [b] using bound (Fin n) p paths simple free
  have rate := offlineRate_le_three_lattice_gap bn bh n1 p1
  have force := lower H sub preserves
  calc
    _ ≤ offlineRate b n p * B := incidence
    _ ≤ ((n : ℝ)^((7-8*b)/10) * ((n : ℝ) + p + (n : ℝ)^(2/3 : ℝ)*(p : ℝ)^(1/2 : ℝ) +
          (n : ℝ)^(1/2 : ℝ)*(p : ℝ)^(2/3 : ℝ) + (n : ℝ)^(2/5 : ℝ)*(p : ℝ)^(3/4 : ℝ)))*B :=
      mul_le_mul_of_nonneg_right rate (by linarith)
    _ ≤ ((n : ℝ)^((7-8*b)/10) * (4718592*H.card))*B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left force (by positivity)) (by linarith)
    _ = _ := by
      change ((n : ℝ)^((7-8*b)/10)*(4718592*H.card))*B = 4718592*B*(n : ℝ)^((7-8*b)/10)*H.card
      ring

/-- The earlier comparison with two lattices remains valid at its
original exponent. -/
theorem theorem14_extremal_lower_with_two_lattice_gap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {n p : ℕ}, 2 ≤ n → 0 < p → p ≤ n^2 →
      ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
        ∀ H ⊆ G, Preserves G H D.toList →
          ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) →
            BridgeFree (ListBefore paths) 4 →
            (∑ i, ((paths i).length : ℝ)) ≤
              C*(n : ℝ)^((1-1/Real.sqrt 2)/2)*H.card := by
  obtain ⟨C,positive,lower⟩ := theorem14_extremal_lower_with_three_lattice_gap
  refine ⟨C,positive,?_⟩
  intro n p hn hp hpCap
  obtain ⟨G,D,dag,size,gap⟩ := lower hn hp hpCap
  refine ⟨G,D,dag,size,?_⟩
  intro H sub preserves paths simple free
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have square : (1/Real.sqrt 2)^2 = (1/2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have bLo : (2/3 : ℝ) ≤ 1/Real.sqrt 2 := by
    apply (sq_le_sq₀ (by norm_num) (by positivity)).mp
    rw [square]
    norm_num
  have exponent : (7-8*(1/Real.sqrt 2))/10 ≤ (1-1/Real.sqrt 2)/2 := by linarith
  have monotone := Real.rpow_le_rpow_of_exponent_le n1 exponent
  exact (gap H sub preserves paths simple free).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left monotone (by linarith)) (by positivity))

/-- The earlier comparison with one lattice remains valid at its
original exponent. -/
theorem theorem14_extremal_lower_with_lattice_gap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {n p : ℕ}, 2 ≤ n → 0 < p → p ≤ n^2 →
      ∃ (G D : Arcs (Fin n)), IsDAG G ∧ D.card = p ∧
        ∀ H ⊆ G, Preserves G H D.toList →
          ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) →
            BridgeFree (ListBefore paths) 4 →
            (∑ i, ((paths i).length : ℝ)) ≤
              C*(n : ℝ)^((2-2*(1/Real.sqrt 2))/3)*H.card := by
  obtain ⟨C,positive,lower⟩ := theorem14_extremal_lower_with_two_lattice_gap
  refine ⟨C,positive,?_⟩
  intro n p hn hp hpCap
  obtain ⟨G,D,dag,size,gap⟩ := lower hn hp hpCap
  refine ⟨G,D,dag,size,?_⟩
  intro H sub preserves paths simple free
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have exponent : (1-1/Real.sqrt 2)/2 ≤ (2-2*(1/Real.sqrt 2))/3 := by
    linarith only [offline_limit_lt]
  have monotone := Real.rpow_le_rpow_of_exponent_le n1 exponent
  exact (gap H sub preserves paths simple free).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left monotone (by linarith)) (by positivity))

end OnlineReachabilityPreservers
