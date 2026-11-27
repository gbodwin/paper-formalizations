import OnlineReachabilityPreservers.LocalOnlineLimit
import OnlineReachabilityPreservers.OfflineLatticeLower
import OnlineReachabilityPreservers.OfflineBridgeExtremalUpper
import OnlineReachabilityPreservers.UnbalancedBridgeExtrema
import OnlineReachabilityPreservers.FrozenBoundaryCases
import OnlineReachabilityPreservers.OutputAverageDistinctCleaning

/-! A quantitative comparison of the last-arc and all-size full extrema. -/

namespace OnlineReachabilityPreservers

open Finset Filter Topology
local notation "Before" => SourceAudit.BeforeIn

private noncomputable def latticeComparisonRate (n p : ℝ) : ℝ :=
  max (n^(2/3:ℝ)*p^(1/2:ℝ)) (max (n^(1/2:ℝ)*p^(2/3:ℝ)) (n^(2/5:ℝ)*p^(3/4:ℝ)))

private theorem first_online_term_le_lattice {n p α : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (lo : 7/10 ≤ α) (hi : α ≤ 701/1000) :
    n^((2+α)/(3+α))*p^(2/(3+α)) ≤ n^(7/50:ℝ)*latticeComparisonRate n p := by
  have nPos : 0 < n := zero_lt_one.trans_le hn
  have pPos : 0 < p := zero_lt_one.trans_le hp
  have den : 0 < 3+α := by linarith
  have nv : (2+α)/(3+α) ≤ 3/4 := (div_le_iff₀ den).mpr (by linarith)
  have pv : 2/(3+α) ≤ 11/20 := (div_le_iff₀ den).mpr (by linarith)
  have coarse : n^((2+α)/(3+α))*p^(2/(3+α)) ≤ n^(3/4:ℝ)*p^(11/20:ℝ) :=
    mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn nv) (Real.rpow_le_rpow_of_exponent_le hp pv)
      (by positivity) (by positivity)
  apply coarse.trans
  by_cases small : p ≤ n
  · have factor : n^(1/12:ℝ)*p^(1/20:ℝ) ≤ n^(7/50:ℝ) := calc
      _ ≤ n^(1/12:ℝ)*n^(1/20:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow pPos.le small (by norm_num)) (by positivity)
      _ = n^(2/15:ℝ) := by rw [← Real.rpow_add nPos]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    calc
      _ = (n^(1/12:ℝ)*p^(1/20:ℝ))*(n^(2/3:ℝ)*p^(1/2:ℝ)) := by
        symm
        rw [mul_mul_mul_comm,← Real.rpow_add nPos,← Real.rpow_add pPos]
        norm_num
      _ ≤ _ := mul_le_mul factor (le_max_left _ _) (by positivity) (by positivity)
  · have factor : n^(1/4:ℝ)*p^(-7/60:ℝ) ≤ n^(7/50:ℝ) := calc
      _ ≤ n^(1/4:ℝ)*n^(-7/60:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos nPos (le_of_lt (lt_of_not_ge small)) (by norm_num)) (by positivity)
      _ = n^(2/15:ℝ) := by rw [← Real.rpow_add nPos]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    calc
      _ = (n^(1/4:ℝ)*p^(-7/60:ℝ))*(n^(1/2:ℝ)*p^(2/3:ℝ)) := by
        symm
        rw [mul_mul_mul_comm,← Real.rpow_add nPos,← Real.rpow_add pPos]
        norm_num
      _ ≤ _ := mul_le_mul factor ((le_max_left _ _).trans (le_max_right _ _)) (by positivity) (by positivity)

private theorem second_online_term_le_lattice {n p α : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (lo : 7/10 ≤ α) (hi : α ≤ 701/1000) :
    n^(2-2*α)*p^α ≤ n^(7/50:ℝ)*latticeComparisonRate n p := by
  have nPos : 0 < n := zero_lt_one.trans_le hn
  have pPos : 0 < p := zero_lt_one.trans_le hp
  have final : 7/10-(4/5)*α ≤ (7/50:ℝ) := by linarith
  by_cases small : p ≤ n^(6/5:ℝ)
  · have factor : n^(3/2-2*α)*p^(α-2/3) ≤ n^(7/50:ℝ) := calc
      _ ≤ n^(3/2-2*α)*(n^(6/5:ℝ))^(α-2/3) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow pPos.le small (by linarith)) (by positivity)
      _ = n^(7/10-(4/5)*α) := by
        rw [← Real.rpow_mul nPos.le,← Real.rpow_add nPos]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn final
    calc
      _ = (n^(3/2-2*α)*p^(α-2/3))*(n^(1/2:ℝ)*p^(2/3:ℝ)) := by
        symm
        rw [mul_mul_mul_comm,← Real.rpow_add nPos,← Real.rpow_add pPos]
        congr 1 <;> congr 1 <;> ring
      _ ≤ _ := mul_le_mul factor ((le_max_left _ _).trans (le_max_right _ _)) (by positivity) (by positivity)
  · have factor : n^(8/5-2*α)*p^(α-3/4) ≤ n^(7/50:ℝ) := calc
      _ ≤ n^(8/5-2*α)*(n^(6/5:ℝ))^(α-3/4) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_lt (lt_of_not_ge small)) (by linarith)) (by positivity)
      _ = n^(7/10-(4/5)*α) := by
        rw [← Real.rpow_mul nPos.le,← Real.rpow_add nPos]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn final
    calc
      _ = (n^(8/5-2*α)*p^(α-3/4))*(n^(2/5:ℝ)*p^(3/4:ℝ)) := by
        symm
        rw [mul_mul_mul_comm,← Real.rpow_add nPos,← Real.rpow_add pPos]
        congr 1 <;> congr 1 <;> ring
      _ ≤ _ := mul_le_mul factor ((le_max_right _ _).trans (le_max_right _ _)) (by positivity) (by positivity)

private theorem lattice_comparison_rate_le_full_maximum {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (pCap : p ≤ n^2)
    (full : Fin p → List (Fin n))
    (maximal : ∀ rows : Fin p → List (Fin n), (∀ i, (rows i).Nodup) → BridgeFree (Before rows) p →
      (∑ i, (rows i).length) ≤ ∑ i, (full i).length) :
    latticeComparisonRate n p ≤ 7077888*((∑ i, (full i).length : ℕ):ℝ) := by
  let M := ∑ i, (full i).length
  obtain ⟨rows,simple,_,all,_,offline⟩ := theorem14_offline_upper_by_bridge_mass n p (by omega) hp
  have rowMass : (∑ i, (rows i).length) ≤ M := maximal rows simple (all p)
  have lower (d : ℕ) (positive : 0 < d) : SourceAudit.multidimensionalLatticeRate d n p ≤
      (3*(24*(2:ℝ)^(d+2)*d*4^(d+2)))*(M:ℝ) := by
    obtain ⟨G,D,_,size,force⟩ := SourceAudit.multidimensional_lattice_lower_all_sizes d positive hn hp pCap
    let H := offlinePreserver G D.toList
    obtain ⟨subset,served,_,bound⟩ := offline (Fin n) G D.toList (Fintype.card_fin n)
      (by simpa only [Finset.length_toList] using size)
    have bounded : (H.card : ℝ) ≤ 3*(M:ℝ) := by
      exact_mod_cast bound.trans (Nat.mul_le_mul_left _ rowMass)
    calc
      _ ≤ (24*(2:ℝ)^(d+2)*d*4^(d+2))*(H.card:ℝ) := force H subset served
      _ ≤ (24*(2:ℝ)^(d+2)*d*4^(d+2))*(3*(M:ℝ)) :=
        mul_le_mul_of_nonneg_left bounded (by positivity)
      _ = _ := by ring
  have first : (n:ℝ)^(2/3:ℝ)*(p:ℝ)^(1/2:ℝ) ≤ 36864*(M:ℝ) := by
    have bound := lower 1 (by decide)
    norm_num [SourceAudit.multidimensionalLatticeRate] at bound ⊢
    exact bound
  have second : (n:ℝ)^(1/2:ℝ)*(p:ℝ)^(2/3:ℝ) ≤ 589824*(M:ℝ) := by
    have bound := lower 2 (by decide)
    norm_num [SourceAudit.multidimensionalLatticeRate] at bound ⊢
    exact bound
  have third : (n:ℝ)^(2/5:ℝ)*(p:ℝ)^(3/4:ℝ) ≤ 7077888*(M:ℝ) := by
    have bound := lower 3 (by decide)
    norm_num [SourceAudit.multidimensionalLatticeRate] at bound ⊢
    exact bound
  exact max_le (first.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)))
    (max_le (second.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))) third)

/-- With positive budgets and any half cutoff at least four, an all-size
full maximizer controls half mass up to `n^(7/50+o(1))` and one constant.
The vanishing slack depends only on the vertex count. -/
theorem indexed_all_full_extremum_controls_half_with_lattice_loss :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ C ≥ (1:ℝ), ∀ {n p cutoff : ℕ}, 0 < n → 0 < p → 4 ≤ cutoff →
      ∃ full : Fin p → List (Fin n), (∀ i, (full i).Nodup) ∧
        (∀ d, IsEmpty (Bridge (Before full) d)) ∧
        (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → (∀ d, IsEmpty (Bridge (Before other) d)) →
          (∑ i, (other i).length) ≤ ∑ i, (full i).length) ∧
        n ≤ (∑ i, (full i).length) ∧ p ≤ (∑ i, (full i).length) ∧
        ∀ half : Fin p → List (Fin n), (∀ i, (half i).Nodup) → HalfBridgeFree (Before half) cutoff →
          (∑ i, ((half i).length:ℝ)) ≤ C*(n:ℝ)^(7/50+ε n)*((∑ i, (full i).length : ℕ):ℝ) := by
  obtain ⟨α,⟨ha,zero⟩,_⟩ := theorem38_root
  obtain ⟨slack,nonnegative,limit,K,K1,online⟩ := theorem38_list_limit.{0} ha zero
  let C : ℝ := 4*7077888*K
  refine ⟨slack,nonnegative,limit,C,by dsimp [C]; linarith,?_⟩
  intro n p cutoff hn hp four
  obtain ⟨full,simple,allowed,maximal,dense,long⟩ := localOrderExtremal_isDense n p p false hn hp
  refine ⟨full,simple,bridgeFree_all_of_cutoff_ge_min allowed (min_le_right _ _),
    fun other simpleOther all => maximal other simpleOther (fun d _ => all d),dense,long,?_⟩
  intro half halfSimple halfFree
  let M := ∑ i, (full i).length
  let m : ℝ := M
  let nR : ℝ := n
  let pR : ℝ := p
  let factor := nR^(7/50+slack n)
  have nOne : 1 ≤ nR := by
    change (1:ℝ) ≤ (n:ℝ)
    exact_mod_cast (show 1 ≤ n by omega)
  have pOne : 1 ≤ pR := by
    change (1:ℝ) ≤ (p:ℝ)
    exact_mod_cast (show 1 ≤ p by omega)
  have nPos : 0 < nR := zero_lt_one.trans_le nOne
  have m0 : 0 ≤ m := by dsimp [m]; positivity
  have nDense : nR ≤ m := by
    change (n:ℝ) ≤ (M:ℝ)
    exact_mod_cast dense
  have pDense : pR ≤ m := by
    change (p:ℝ) ≤ (M:ℝ)
    exact_mod_cast long
  have factorOne : 1 ≤ factor := Real.one_le_rpow nOne (by linarith [nonnegative n])
  have baseline : m ≤ factor*7077888*m := le_mul_of_one_le_left m0 (by linarith only [factorOne])
  change (∑ i, ((half i).length:ℝ)) ≤ C*factor*m
  by_cases lattice : 2 ≤ n ∧ p ≤ n^2
  · have rate : latticeComparisonRate nR pR ≤ 7077888*m :=
      lattice_comparison_rate_le_full_maximum lattice.1 hp lattice.2 full maximal
    have term (a b : ℝ) (withLattice : nR^a*pR^b ≤ nR^(7/50:ℝ)*latticeComparisonRate nR pR) :
        nR^(a+slack n)*pR^b ≤ factor*7077888*m := calc
      _ = nR^(slack n)*(nR^a*pR^b) := by
        rw [add_comm a,Real.rpow_add nPos,mul_assoc]
      _ ≤ nR^(slack n)*(nR^(7/50:ℝ)*latticeComparisonRate nR pR) :=
        mul_le_mul_of_nonneg_left withLattice (by positivity)
      _ = factor*latticeComparisonRate nR pR := by
        rw [← mul_assoc,← Real.rpow_add nPos,add_comm (slack n)]
      _ ≤ factor*(7077888*m) := mul_le_mul_of_nonneg_left rate (by positivity)
      _ = _ := by ring
    have first := term ((2+α)/(3+α)) (2/(3+α)) (first_online_term_le_lattice nOne pOne ha.1.le ha.2.le)
    have second := term (2-2*α) α (second_online_term_le_lattice nOne pOne ha.1.le ha.2.le)
    have onlineHalf := online (Fin n) p half halfSimple (fun d size => halfFree (size.trans four))
    simp only [Fintype.card_fin] at onlineHalf
    have combined : nR+nR^((2+α)/(3+α)+slack n)*pR^(2/(3+α))+
        nR^(2-2*α+slack n)*pR^α+pR ≤ 4*(factor*7077888*m) := by
      linarith only [nDense.trans baseline,pDense.trans baseline,first,second]
    exact onlineHalf.trans ((mul_le_mul_of_nonneg_left combined (zero_le_one.trans K1)).trans_eq (by unfold C; ring))
  · have many : 2*(n*n-n) ≤ (3:ℕ)*(3-1)*p := by
      by_cases small : n < 2
      · have one : n = 1 := by omega
        simp [one]
      · have pLarge : n^2 < p := Nat.lt_of_not_ge (fun h => lattice ⟨by omega,h⟩)
        rw [pow_two] at pLarge
        have pairs : n*n-n ≤ p := (Nat.sub_le _ _).trans pLarge.le
        omega
    have bounded := halfBridgeFree_mass_le_of_unbalanced_budgets half halfSimple halfFree
      (by omega) hn hp (by decide : 3 ≤ 3) (Or.inl many)
    have small : (∑ i, ((half i).length:ℝ)) ≤ 3*m := by
      change (∑ i, ((half i).length:ℝ)) ≤ 3*(M:ℝ)
      exact_mod_cast bounded.trans (Nat.mul_le_mul_left _ (max_le dense long))
    calc
      _ ≤ 3*m := small
      _ ≤ 3*(factor*7077888*m) := mul_le_mul_of_nonneg_left baseline (by norm_num)
      _ ≤ (4*K)*(factor*7077888*m) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by unfold C; ring

/-- With literal half-free input, the same power loss gives distinct
nonempty all-size full rows within both budgets and the four caps at
their own averages. Only the numerical constant grows in the transfer. -/
theorem literal_full_witness_controls_half_with_lattice_loss :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ C ≥ (1:ℝ), ∀ {n p cutoff : ℕ}, 0 < n → 0 < p → 4 ≤ cutoff →
        ∀ half : Fin p → List (Fin n), Function.Injective half → (∀ i, half i ≠ [] ∧ (half i).Nodup) →
        HalfBridgeFree (Before half) cutoff →
        ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
          Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧
          (∀ d, IsEmpty (Bridge (Before clean) d)) ∧ listOutputAverageCaps clean ∧
          (∑ i, ((half i).length:ℝ)) ≤ C*(n:ℝ)^(7/50+ε n)*((∑ i, (clean i).length : ℕ):ℝ) := by
  obtain ⟨ε,nonnegative,limit,C,C1,comparison⟩ := indexed_all_full_extremum_controls_half_with_lattice_loss
  refine ⟨ε,nonnegative,limit,C*9414,by linarith,?_⟩
  intro n p cutoff hn hp four half distinct rows free
  obtain ⟨full,simple,all,_,dense,long,compared⟩ := comparison hn hp four
  let M := ∑ i, (full i).length
  let outputCutoff := max 2 p
  have pCap := distinctPathCount_le_square half distinct (fun i => (rows i).1) (fun i => (rows i).2)
    (by omega) free
  have indexed : ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) outputCutoff ∧
      M ≤ 523*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
    obtain ⟨v,vFits,q,qFits,clean,cleanSimple,allFree,keeps,within,caps⟩ :=
      regularization_list_output_average_full_all full simple all hn hp dense long
    exact ⟨v,vFits,q,qFits,clean,cleanSimple,fun d _ => allFree d,keeps,within,caps⟩
  obtain ⟨v,vFits,q,qFits,clean,injective,present,cleanSimple,cleanFree,keeps,_,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed_budget (half := false) (k := outputCutoff)
      (retention := 523) (le_max_left _ _) hn hp dense long pCap indexed
  refine ⟨v,vFits,q,qFits,clean,injective,fun i => ⟨present i,cleanSimple i⟩,
    bridgeFree_all_of_cutoff_ge_min cleanFree ((min_le_right _ _).trans (qFits.trans (le_max_right _ _))),caps,?_⟩
  have retention : (M:ℝ) ≤ 9414*((∑ i, (clean i).length : ℕ):ℝ) := by exact_mod_cast keeps
  calc
    _ ≤ C*(n:ℝ)^(7/50+ε n)*(M:ℝ) := compared half (fun i => (rows i).2) free
    _ ≤ C*(n:ℝ)^(7/50+ε n)*(9414*((∑ i, (clean i).length : ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left retention (mul_nonneg (zero_le_one.trans C1) (by positivity))
    _ = _ := by ring

end OnlineReachabilityPreservers
