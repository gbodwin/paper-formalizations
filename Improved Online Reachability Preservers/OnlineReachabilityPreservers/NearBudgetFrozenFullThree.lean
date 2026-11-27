import OnlineReachabilityPreservers.FrozenWengerThree
import OnlineReachabilityPreservers.ExtremalCopyBounds

/-! The literal frozen full-three witness for sufficiently large nearby budgets. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- The half-three mass is at most `4 min(n,p) q` when both budgets
are within factor `65/64` and the smaller budget is below `8 q³`. -/
theorem half_three_mass_le_four_min_q_of_near_large_budgets {n p q k : ℕ}
    (hn : 0 < n) (hp : 0 < p) (nClose : 64*n ≤ 65*p) (pClose : 64*p ≤ 65*n)
    (large : 512 ≤ q) (envelope : min n p < 8*q^3)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    (∑ i, (paths i).length) ≤ 4*(min n p)*q := by
  let b := min n p
  let M := ∑ i, (paths i).length
  let S := M-M/16-(16*n+p)
  have cube : S^3 ≤ 6*(n*p)^2 :=
    half_three_latest_intersection_shifted_mass_cube_le hn hp paths simple half three 15
  have nCap : 64*n ≤ 65*b := by
    rcases le_total n p with h | h
    · rw [show b = n from min_eq_left h]; omega
    · rw [show b = p from min_eq_right h]; exact nClose
  have pCap : 64*p ≤ 65*b := by
    rcases le_total n p with h | h
    · rw [show b = n from min_eq_left h]; exact pClose
    · rw [show b = p from min_eq_right h]; omega
  have charge : 16*n+p ≤ 18*b := by omega
  have pScale : 64*(n*p) ≤ 65*b^2 := by
    rcases le_total n p with smaller | larger
    · rw [show b = n from min_eq_left smaller,pow_two]
      calc
        64*(n*p) = n*(64*p) := by ring
        _ ≤ n*(65*n) := Nat.mul_le_mul_left _ pClose
        _ = _ := by ring
    · rw [show b = p from min_eq_right larger,pow_two]
      calc
        64*(n*p) = p*(64*n) := by ring
        _ ≤ p*(65*p) := Nat.mul_le_mul_left _ nClose
        _ = _ := by ring
  have square : 64^2*(n*p)^2 ≤ 65^2*b^4 := calc
    _ = (64*(n*p))^2 := by ring
    _ ≤ (65*b^2)^2 := Nat.pow_le_pow_left pScale 2
    _ = _ := by ring
  by_contra! tooLarge
  have factor : 432*b ≤ b*q := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left b (show 432 ≤ q by omega)
  have floor : 16*(M/16) ≤ M := Nat.mul_div_le _ _
  have excess : 4*(b*q) < M := by convert tooLarge using 1; ring
  have gap : 89*(b*q) < 24*S := by dsimp only [S]; omega
  have cap : 64^2*(24*S)^3 ≤ 64^2*(89*(b*q))^3 := calc
    _ = (24^3)*(64^2*S^3) := by ring
    _ ≤ 82944*(64^2*(n*p)^2) := by
      convert Nat.mul_le_mul_left (24^3) (Nat.mul_le_mul_left (64^2) cube) using 1
      ring
    _ ≤ 82944*(65^2*b^4) := Nat.mul_le_mul_left _ square
    _ = (82944*65^2)*(b*b^3) := by ring
    _ ≤ (82944*65^2)*((8*q^3)*b^3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ envelope.le)
    _ = (663552*65^2)*(b*q)^3 := by ring
    _ ≤ (64^2*89^3)*(b*q)^3 := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring
  have larger := pow_lt_pow_left₀ gap (Nat.zero_le _) (by decide : 3 ≠ 0)
  exact (not_lt_of_ge cap) (Nat.mul_lt_mul_of_pos_left larger (by decide))

/-- At cutoff three the literal half maximum exists at sufficiently large
nearby budgets. A full-three family within both budgets keeps at least
one thirty-second of it and meets the four starting-average caps. -/
theorem localOrderDistinctExtremal_frozen_full_three_at_near_large_budgets {n p : ℕ}
    (large : 512^3 ≤ min n p) (nClose : 64*n ≤ 65*p) (pClose : 64*p ≤ 65*n) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ q : ℕ, q^3 ≤ min n p ∧ ∃ rows : Fin (q^3) → List (Fin (q^3)),
        Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) = q^4 ∧ (∑ i, (rows i).length) ≤ M ∧ M ≤ 32*(∑ i, (rows i).length) ∧
        frozenListCaps n p M rows := by
  let b := min n p
  let a := max n p
  have bPos : 0 < b := Nat.lt_of_lt_of_le (by decide) large
  have bn : b ≤ n := min_le_left _ _
  have bp : b ≤ p := min_le_right _ _
  have na : n ≤ a := le_max_left _ _
  have pa : p ≤ a := le_max_right _ _
  have scale : 64*a ≤ 65*b := by
    rcases le_total n p with h | h
    · simpa only [a,b,max_eq_right h,min_eq_left h] using pClose
    · simpa only [a,b,max_eq_left h,min_eq_right h] using nClose
  let m := Nat.log 8 b
  let q := 2^m
  have size : 9 ≤ m := Nat.le_log_of_pow_le (by decide) (by exact large)
  have largeQ : 512 ≤ q := Nat.pow_le_pow_right (by decide : 0 < 2) size
  have cubePower : q^3 = 8^m := by dsimp only [q]; rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have fit : q^3 ≤ b := cubePower.trans_le (Nat.pow_log_le_self 8 bPos.ne')
  have envelope : b < 8*q^3 := by
    calc
      _ < 8^(m+1) := Nat.lt_pow_succ_log_self (by decide : 1 < 8) b
      _ = _ := by rw [cubePower,pow_succ,Nat.mul_comm]
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let K := GaloisField 2 m
  let : Fintype K := Fintype.ofFinite K
  have card : Fintype.card K = q := (Nat.card_eq_fintype_card).symm.trans (GaloisField.card 2 m (by omega))
  let FieldWitness (r : ℕ) : Prop := ∃ rows : Fin (r^3) → List (Fin (r^3)), Function.Injective rows ∧
    (∀ i, (rows i).Nodup ∧ (rows i).length = r) ∧ BridgeFree (Before rows) 3 ∧
    (∑ i, (rows i).length) = r^4 ∧ (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = r) ∧
    listOutputAverageCaps rows
  obtain ⟨rows,injective,lengths,free,mass,degree,_⟩ :=
    (card ▸ (show FieldWitness (Fintype.card K) from wenger_full_three_rows K) : FieldWitness q)
  have long (i : Fin (q^3)) : 2 ≤ (rows i).length := by rw [(lengths i).2]; omega
  have present (i : Fin (q^3)) : rows i ≠ [] ∧ (rows i).Nodup :=
    ⟨List.length_pos_iff.mp (lt_of_lt_of_le (by decide) (long i)),(lengths i).1⟩
  let copies := if a ≤ 4*q^3 then 1 else if a ≤ 8*q^3 then 2 else 3
  have copiesFit : copies*q^3 ≤ b := by
    dsimp only [copies]
    split
    · simpa using fit
    · split <;> omega
  have copiesPos : 1 ≤ copies := by
    dsimp only [copies]
    split
    · decide
    · split <;> decide
  have copiesMass : a*q ≤ 4*(copies*q^4) := by
    have aCap : a ≤ 4*copies*q^3 := by
      dsimp only [copies]
      split
      · omega
      · split <;> omega
    calc
      _ ≤ (4*copies*q^3)*q := Nat.mul_le_mul_right _ aCap
      _ = _ := by ring
  have spare : p-copies*q^3 ≤ n := by
    have oneCopy : q^3 ≤ copies*q^3 := Nat.le_mul_of_pos_left _ (by omega)
    rcases le_total p n with h | h
    · omega
    · have smallN : n < 8*q^3 := by simpa only [b,min_eq_left h] using envelope
      omega
  obtain ⟨candidate,candidateDistinct,candidateRows,candidateFree,candidateMass⟩ :=
    exists_literal_full_disjoint_copies_with_singletons rows (fun i => (lengths i).1) long (by decide) free
      (copiesFit.trans bn) (copiesFit.trans bp) spare
  obtain ⟨paths,distinct,valid,half,maximal,_,_⟩ :=
    localOrderDistinctExtremal_isDense (n := n) (p := p) (k := 3) true (bPos.trans_le bp)
      ⟨candidate,candidateDistinct,candidateRows,candidateFree.halfFree⟩
  let M := ∑ i, (paths i).length
  have copiesLe : copies*q^4 ≤ M := by
    rw [← mass]
    exact candidateMass.trans (maximal candidate candidateDistinct candidateRows candidateFree.halfFree)
  have witnessLe : q^4 ≤ M := (Nat.le_mul_of_pos_left _ (by omega)).trans copiesLe
  have volume : a*q ≤ 4*M := copiesMass.trans (Nat.mul_le_mul_left _ copiesLe)
  have upper : M ≤ 4*b*q := half_three_mass_le_four_min_q_of_near_large_budgets (bPos.trans_le bn)
    (bPos.trans_le bp) nClose pClose largeQ envelope paths (fun i => (valid i).2) half le_rfl
  have retain : M ≤ 32*q^4 := calc
    _ ≤ 4*b*q := upper
    _ ≤ 4*(8*q^3)*q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ envelope.le)
    _ = _ := by ring
  have lowerCap {N : ℕ} (h : b ≤ N) : (M:ℝ)/(4*(N:ℝ)) ≤ q := by
    have positive : 0 < (N:ℝ) := Nat.cast_pos.mpr (bPos.trans_le h)
    apply (div_le_iff₀ (by positivity)).mpr
    have arithmetic : (M:ℝ) ≤ 4*(N:ℝ)*q := by
      exact_mod_cast upper.trans (Nat.mul_le_mul_right q (Nat.mul_le_mul_left 4 h))
    convert arithmetic using 1
    ring
  have upperCap {N : ℕ} (lo : b ≤ N) (hi : N ≤ a) : (q:ℝ) ≤ 4*(M:ℝ)/N := by
    have positive : 0 < (N:ℝ) := Nat.cast_pos.mpr (bPos.trans_le lo)
    apply (le_div_iff₀ positive).mpr
    have arithmetic : (N:ℝ)*q ≤ 4*(M:ℝ) := by
      exact_mod_cast (Nat.mul_le_mul_right q hi).trans volume
    simpa only [mul_comm (q:ℝ)] using arithmetic
  have caps : frozenListCaps n p M rows := by
    simp only [frozenListCaps,degree,fun i => (lengths i).2]
    exact ⟨fun _ => ⟨lowerCap bn,upperCap bn na⟩,fun _ => ⟨lowerCap bp,upperCap bp pa⟩⟩
  exact ⟨paths,distinct,valid,half,maximal,q,fit,rows,injective,present,free,mass,
    mass.trans_le witnessLe,by rw [mass]; exact retain,caps⟩

end OnlineReachabilityPreservers
