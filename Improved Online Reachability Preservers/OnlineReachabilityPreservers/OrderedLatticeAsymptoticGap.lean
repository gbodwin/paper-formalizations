import OnlineReachabilityPreservers.LocalOnlineBound
import OnlineReachabilityPreservers.OrderedLatticeBridgeAudit

/-! A polynomial separation of the two ordered bridge exclusions. -/

namespace OnlineReachabilityPreservers

open Finset Filter
open scoped Topology
local notation "Before" => SourceAudit.BeforeIn

/-- At both budgets at most `m`, the half-four incidence bound has a
uniform diagonal exponent of at most thirteen tenths. -/
theorem theorem38_list_diagonal_upper :
    ∃ K ≥ (1:ℝ), ∀ {n p m : ℕ}, 1 ≤ m → n ≤ m → p ≤ m →
      ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) 4 →
      (∑ i, ((paths i).length : ℝ)) ≤ K * (m:ℝ) ^ (13/10:ℝ) := by
  obtain ⟨α, ⟨interval,root⟩,_⟩ := theorem38_root
  obtain ⟨_,second,first,limit,_⟩ := theorem38_exponent_limits interval root
  obtain ⟨iteration,large⟩ := (limit.eventually (Ioi_mem_nhds interval.1)).exists
  let a := onlineFirstExponent iteration
  let b := onlineSecondExponent iteration
  have aNonneg : 0 ≤ a := (by norm_num : (0:ℝ) ≤ 8/11).trans (first iteration).1
  have aUnit : a ≤ 1 := (first iteration).2.le.trans (by norm_num)
  have bNonneg : 0 ≤ b := (by norm_num : (0:ℝ) ≤ 2/3).trans (second iteration).1
  have bUnit : b ≤ 1 := ((second iteration).2.trans interval.2).le.trans (by norm_num)
  obtain ⟨K,Kone,bound⟩ := theorem38_list_iteration iteration
  refine ⟨K,Kone,?_⟩
  intro n p m positive vertices rows paths simple free
  let x : ℝ := m
  have one : 1 ≤ x := by
    change (1:ℝ) ≤ (m:ℝ)
    exact_mod_cast positive
  have pos : 0 < x := zero_lt_one.trans_le one
  have mono := onlineRate_mono aNonneg aUnit bNonneg bUnit
    (Nat.cast_nonneg n) (Nat.cast_nonneg p) (show (n:ℝ) ≤ x from Nat.cast_le.mpr vertices)
    (show (p:ℝ) ≤ x from Nat.cast_le.mpr rows)
  have linear : x ≤ x ^ (13/10:ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le one (by norm_num : (1:ℝ) ≤ 13/10))
  have lead : x^a*x^(2-2*a) ≤ x ^ (13/10:ℝ) := by
    rw [← Real.rpow_add pos]
    exact Real.rpow_le_rpow_of_exponent_le one (by linarith only [(first iteration).1])
  have middle : x^(2-2*b)*x^b ≤ x ^ (13/10:ℝ) := by
    rw [← Real.rpow_add pos]
    exact Real.rpow_le_rpow_of_exponent_le one (by change 7/10 < b at large; linarith only [large])
  have diagonal : onlineRate a b x x ≤ x ^ (13/10:ℝ) :=
    max_le linear (max_le lead (max_le middle linear))
  have input := bound (Fin n) p paths simple free
  rw [Fintype.card_fin] at input
  exact input.trans (mul_le_mul_of_nonneg_left (mono.trans diagonal) (zero_le_one.trans Kone))

/-- The first two layers distinguish the starting row and slope of a
positive-length lattice line. -/
theorem orderedLatticeRows_injective_of_steps {steps rows slopes starts : ℕ}
    (fit : LatticeFits steps rows slopes starts) (positive : 0 < steps) :
    Function.Injective (orderedLatticeRows fit) := by
  intro a b equal
  have functions := List.ofFn_inj.mp equal
  have start := congrArg (fun f : Fin (steps+1) → LayerGrid steps rows => (f 0).2.val) functions
  let next : Fin (steps+1) := ⟨1,by omega⟩
  have nextRows := congrArg (fun f : Fin (steps+1) → LayerGrid steps rows => (f next).2.val) functions
  change (ofLex a).2.val + 0 * (ofLex a).1.val = (ofLex b).2.val + 0 * (ofLex b).1.val at start
  change (ofLex a).2.val + 1 * (ofLex a).1.val = (ofLex b).2.val + 1 * (ofLex b).1.val at nextRows
  exact ofLex.injective (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))

/-- The slope-ordered lattice excludes bridges with all arcs earlier than
their river at every size. Its mass is at least a constant times
`t^(1/10)` times every half-four-free mass at those budgets. -/
theorem ordered_lattice_polynomial_gap_over_half_four :
    ∃ A ≥ (1:ℝ), ∀ t : ℕ, 0 < t → ∃ fit : LatticeFits t (2*t^2) t (t^2),
      Function.Injective (orderedLatticeRows fit) ∧
      (∀ ℓ, (orderedLatticeRows fit ℓ).Nodup ∧ (orderedLatticeRows fit ℓ).length = t+1) ∧
      (∀ d (b : Bridge (Before (orderedLatticeRows fit)) d), ¬ ∀ i, b.arc i < b.river) ∧
      ∀ {n p : ℕ}, n ≤ (t+1)*(2*t^2) → p ≤ t^3 → ∀ paths : Fin p → List (Fin n),
        (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) 4 →
        (t:ℝ) ^ (1/10:ℝ) * (∑ i, ((paths i).length : ℝ)) ≤
          A * ∑ ℓ, ((orderedLatticeRows fit ℓ).length : ℝ) := by
  obtain ⟨K,Kone,bound⟩ := theorem38_list_diagonal_upper
  have Knonneg : 0 ≤ K := zero_le_one.trans Kone
  refine ⟨16*K,by linarith,?_⟩
  intro t positive
  have fit : LatticeFits t (2*t^2) t (t^2) := by
    unfold LatticeFits
    have bounded := Nat.mul_le_mul_left t (Nat.sub_le t 1)
    nlinarith only [bounded]
  refine ⟨fit,orderedLatticeRows_injective_of_steps fit positive,?_,?_,?_⟩
  · intro ℓ
    exact ⟨orderedLatticeRows_simple fit ℓ,List.length_ofFn⟩
  · intro d bridge
    exact orderedLatticeRows_no_bridge_with_all_arcs_earlier fit bridge
  · intro n p vertices rows paths simple free
    let m := 4*t^3
    have vertexUpper : (t+1)*(2*t^2) ≤ m := by
      have factor : t+1 ≤ 2*t := by omega
      exact (Nat.mul_le_mul_right (2*t^2) factor).trans_eq (by dsimp [m]; ring)
    have rowUpper : t^3 ≤ m := by dsimp only [m]; omega
    have mOne : 1 ≤ m := lt_of_lt_of_le (pow_pos positive 3) rowUpper
    have estimate := bound mOne (vertices.trans vertexUpper) (rows.trans rowUpper) paths simple free
    have tPos : (0:ℝ) < t := by exact_mod_cast positive
    have scale : (m:ℝ) ^ (13/10:ℝ) ≤ 16 * (t:ℝ) ^ (39/10:ℝ) := by
      push_cast [m]
      rw [Real.mul_rpow (by norm_num : 0 ≤ (4:ℝ)) (by positivity), ← Real.rpow_natCast_mul tPos.le]
      norm_num only [Nat.cast_ofNat, show (3:ℝ)*(13/10)=39/10 by norm_num]
      exact mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
          (by norm_num : (13/10:ℝ) ≤ 2)).trans_eq (by norm_num)) (by positivity)
    have count : Fintype.card (LatticeLine t (t^2)) = t^3 := by
      rw [← Fintype.card_congr (toLex : (Fin t × Fin (t^2)) ≃ LatticeLine t (t^2)),
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      ring
    have mass : (∑ ℓ, ((orderedLatticeRows fit ℓ).length : ℝ)) = ((t:ℝ)+1)*(t:ℝ)^3 := by
      simp only [orderedLatticeRows,List.length_ofFn,sum_const,card_univ,count,nsmul_eq_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
      ring
    calc
      _ ≤ (t:ℝ) ^ (1/10:ℝ) * (K * (m:ℝ) ^ (13/10:ℝ)) :=
        mul_le_mul_of_nonneg_left estimate (by positivity)
      _ ≤ (t:ℝ) ^ (1/10:ℝ) * (K * (16 * (t:ℝ) ^ (39/10:ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left scale Knonneg) (by positivity)
      _ = (16*K)*((t:ℝ) ^ (1/10:ℝ) * (t:ℝ) ^ (39/10:ℝ)) := by ring
      _ = (16*K)*(t:ℝ)^4 := by
        rw [← Real.rpow_add tPos,show (1/10:ℝ)+39/10=(4:ℕ) by norm_num,Real.rpow_natCast]
      _ ≤ (16*K)*∑ ℓ, ((orderedLatticeRows fit ℓ).length : ℝ) := by
        rw [mass,show ((t:ℝ)^4) = (t:ℝ)*(t:ℝ)^3 by ring]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)

/-- No fixed factor compares the slope-ordered lattice mass to all
half-four-free masses at the same budgets. -/
theorem ordered_lattice_unbounded_gap_over_half_four (C : ℝ) (nonneg : 0 ≤ C) :
    ∃ t : ℕ, 0 < t ∧ ∃ fit : LatticeFits t (2*t^2) t (t^2),
      Function.Injective (orderedLatticeRows fit) ∧
      (∀ ℓ, (orderedLatticeRows fit ℓ).Nodup ∧ (orderedLatticeRows fit ℓ).length = t+1) ∧
      (∀ d (b : Bridge (Before (orderedLatticeRows fit)) d), ¬ ∀ i, b.arc i < b.river) ∧
      ∀ {n p : ℕ}, n ≤ (t+1)*(2*t^2) → p ≤ t^3 → ∀ paths : Fin p → List (Fin n),
        (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) 4 →
        C * (∑ i, ((paths i).length : ℝ)) < ∑ ℓ, ((orderedLatticeRows fit ℓ).length : ℝ) := by
  obtain ⟨A,Aone,bound⟩ := ordered_lattice_polynomial_gap_over_half_four
  have Apos : 0 < A := zero_lt_one.trans_le Aone
  obtain ⟨r,big⟩ := exists_nat_gt (C*A)
  have rPos : (0:ℝ) < r := lt_of_le_of_lt (mul_nonneg nonneg Apos.le) big
  let t := r^10
  have positive : 0 < t := pow_pos (by exact_mod_cast rPos) _
  obtain ⟨fit,distinct,simple,earlier,gap⟩ := bound t positive
  refine ⟨t,positive,fit,distinct,simple,earlier,?_⟩
  intro n p vertices rows paths pathSimple free
  have estimate := gap vertices rows paths pathSimple free
  have factor : (t:ℝ) ^ (1/10:ℝ) = r := by
    push_cast [t]
    rw [← Real.rpow_natCast_mul rPos.le,show ((10:ℕ):ℝ)*(1/10)=1 by norm_num,Real.rpow_one]
  rw [factor] at estimate
  by_cases empty : (∑ i, ((paths i).length : ℝ)) = 0
  · rw [empty,mul_zero]
    let ℓ : LatticeLine t (t^2) := toLex (⟨0,positive⟩,⟨0,pow_pos positive 2⟩)
    have length : 0 < ((orderedLatticeRows fit ℓ).length : ℝ) := by rw [(simple ℓ).2]; positivity
    exact length.trans_le (single_le_sum (fun i _ => Nat.cast_nonneg (orderedLatticeRows fit i).length) (mem_univ ℓ))
  · have massPos : 0 < ∑ i, ((paths i).length : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm empty)
    have strict : A * (C * ∑ i, ((paths i).length : ℝ)) <
        A * ∑ ℓ, ((orderedLatticeRows fit ℓ).length : ℝ) := calc
      _ = (C*A)*(∑ i, ((paths i).length : ℝ)) := by ring
      _ < (r:ℝ)*(∑ i, ((paths i).length : ℝ)) := mul_lt_mul_of_pos_right big massPos
      _ ≤ _ := estimate
    exact lt_of_not_ge fun reverse => strict.not_ge (mul_le_mul_of_nonneg_left reverse Apos.le)

end OnlineReachabilityPreservers
