import OnlineReachabilityPreservers.WengerThreeRows
import OnlineReachabilityPreservers.ExtremalCopyBounds

/-! The starting-average witness at cutoff three for comparable budgets. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private theorem comparable_min_budget {n p : ℕ} (nClose : 2*n ≤ 3*p) (pClose : 2*p ≤ 3*n) :
    2*n ≤ 3*min n p ∧ 2*p ≤ 3*min n p := by
  rcases le_total n p with order | order
  · rw [min_eq_left order]
    exact ⟨by omega,pClose⟩
  · rw [min_eq_right order]
    exact ⟨nClose,by omega⟩

/-- The latest-common-vertex count controls the half mass at a width
whose cube is at least sixteen sixty-fifths of the smaller budget. -/
theorem half_three_mass_le_four_min_width_of_comparable_budgets {n p width cutoff : ℕ}
    (hn : 0 < n) (hp : 0 < p) (nClose : 2*n ≤ 3*p) (pClose : 2*p ≤ 3*n)
    (large : 1024 ≤ width) (envelope : 16*min n p ≤ 65*width^3)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) :
    (∑ i, (paths i).length) ≤ 4*(min n p)*width := by
  let b := min n p
  let M := ∑ i, (paths i).length
  let S := M-M/32-(32*n+p)
  have cube : S^3 ≤ 6*(n*p)^2 :=
    half_three_latest_intersection_shifted_mass_cube_le hn hp paths simple half three 31
  obtain ⟨nCap,pCap⟩ := comparable_min_budget nClose pClose
  change 2*n ≤ 3*b at nCap
  change 2*p ≤ 3*b at pCap
  have charge : 32*n+p ≤ 50*b := by omega
  have product : 2*(n*p) ≤ 3*b^2 := by
    rcases le_total n p with h | h
    · rw [show b = n from min_eq_left h,pow_two]
      calc
        _ = n*(2*p) := by ring
        _ ≤ n*(3*n) := Nat.mul_le_mul_left _ pClose
        _ = _ := by ring
    · rw [show b = p from min_eq_right h,pow_two]
      calc
        _ = p*(2*n) := by ring
        _ ≤ p*(3*p) := Nat.mul_le_mul_left _ nClose
        _ = _ := by ring
  have square : 4*(n*p)^2 ≤ 9*b^4 := calc
    _ = (2*(n*p))^2 := by ring
    _ ≤ (3*b^2)^2 := Nat.pow_le_pow_left product 2
    _ = _ := by ring
  by_contra! excess
  have scale : 800*b ≤ b*width := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left b (show 800 ≤ width by omega)
  have floor : 32*(M/32) ≤ M := Nat.mul_div_le _ _
  have above : 4*(b*width) < M := by convert excess using 1; ring
  have gap : 61*(b*width) < 16*S := by dsimp only [S]; omega
  have cap : 64*(16*S)^3 ≤ 64*(61*(b*width))^3 := calc
    _ = 16^4*(4*S^3) := by ring
    _ ≤ (16^4*6)*(4*(n*p)^2) := by
      convert Nat.mul_le_mul_left (16^4) (Nat.mul_le_mul_left 4 cube) using 1
      ring
    _ ≤ (16^4*6)*(9*b^4) := Nat.mul_le_mul_left _ square
    _ = (16^3*6*9)*((16*b)*b^3) := by ring
    _ ≤ (16^3*6*9)*((65*width^3)*b^3) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ envelope)
    _ = (16^3*6*9*65)*(b*width)^3 := by ring
    _ ≤ (64*61^3)*(b*width)^3 := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring
  exact (not_lt_of_ge cap) (Nat.mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ gap (Nat.zero_le _) (by decide : 3 ≠ 0)) (by decide))

private theorem exists_wenger_width_scale {b : ℕ} (large : 1024^3 ≤ b) :
    ∃ m width : ℕ, 0 < m ∧ 1024 ≤ width ∧ width ≤ 2^m ∧
      width*(2^m)^2 ≤ b ∧ b ≤ 4*(width*(2^m)^2) ∧ 16*b ≤ 65*width^3 := by
  let m := Nat.log 8 b
  let q := 2^m
  have bPos : 0 < b := Nat.lt_of_lt_of_le (by decide) large
  have size : 10 ≤ m := Nat.le_log_of_pow_le (by decide) (by exact large)
  have qLarge : 1024 ≤ q := Nat.pow_le_pow_right (by decide : 0 < 2) size
  have power : q^3 = 8^m := by dsimp only [q]; rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have lower : q^3 ≤ b := power.trans_le (Nat.pow_log_le_self 8 bPos.ne')
  have upper : b < 8*q^3 := calc
    _ < 8^(m+1) := Nat.lt_pow_succ_log_self (by decide : 1 < 8) b
    _ = _ := by rw [power,pow_succ,Nat.mul_comm]
  by_cases small : b ≤ 4*q^3
  · have volume : q*q^2 = q^3 := by ring
    refine ⟨m,q,by omega,qLarge,le_rfl,?_,?_,by omega⟩
    · change q*q^2 ≤ b
      rwa [volume]
    · change b ≤ 4*(q*q^2)
      rwa [volume]
  · let r := 2*q
    let width := b/r^2
    have rEq : 2^(m+1) = r := by simp [r,q,pow_succ,Nat.mul_comm]
    have squarePos : 0 < r^2 := by dsimp only [r]; positivity
    have widthLo : q ≤ width := (Nat.le_div_iff_mul_le squarePos).mpr (by
      calc
        _ = 4*q^3 := by dsimp only [r]; ring
        _ ≤ _ := by omega)
    have widthLarge := qLarge.trans widthLo
    have fit : width*r^2 ≤ b := Nat.div_mul_le_self _ _
    have last : b < (width+1)*r^2 := by
      simpa only [width,Nat.mul_comm] using Nat.lt_mul_div_succ b squarePos
    have widthHi : width ≤ r := by
      apply Nat.le_of_mul_le_mul_right _ squarePos
      exact fit.trans (show b ≤ r*r^2 by dsimp only [r]; convert upper.le using 1; ring)
    have envelope : b ≤ 4*(width*r^2) := calc
      _ ≤ (width+1)*r^2 := last.le
      _ ≤ (4*width)*r^2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
    have cube : 16*b ≤ 65*width^3 := calc
      _ ≤ 16*((width+1)*r^2) := Nat.mul_le_mul_left _ last.le
      _ = (64*(width+1))*q^2 := by dsimp only [r]; ring
      _ ≤ (65*width)*width^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left widthLo 2)
      _ = _ := by ring
    exact ⟨m+1,width,by omega,widthLarge,by rw [rEq]; exact widthHi,
      by rw [rEq]; exact fit,by rw [rEq]; exact envelope,cube⟩

/-- At cutoff three, when the smaller budget is at least `1024³` and
the budgets differ by at most a factor of three halves, the literal
half maximum exists. A full-three witness meets both budgets and all
four starting-average caps, retaining at least a sixteenth of it. -/
theorem localOrderDistinctExtremal_frozen_full_three_at_comparable_large_budgets {n p : ℕ}
    (large : 1024^3 ≤ min n p) (nClose : 2*n ≤ 3*p) (pClose : 2*p ≤ 3*n) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ v ≤ min n p, ∃ rows : Fin v → List (Fin v),
        Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) ≤ M ∧ M ≤ 16*(∑ i, (rows i).length) ∧
        frozenListCaps n p M rows := by
  let b := min n p
  have bPos : 0 < b := Nat.lt_of_lt_of_le (by decide) large
  have bn : b ≤ n := min_le_left _ _
  have bp : b ≤ p := min_le_right _ _
  have hn := bPos.trans_le bn
  have hp := bPos.trans_le bp
  obtain ⟨m,width,mPos,widthLarge,widthFit,fit,envelope,cubic⟩ := exists_wenger_width_scale large
  let v := width*(2^m)^2
  have widthPos : 0 < width := by omega
  have vPos : 0 < v := by dsimp only [v]; positivity
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let K := GaloisField 2 m
  let : Fintype K := Fintype.ofFinite K
  have card : Fintype.card K = 2^m := (Nat.card_eq_fintype_card).symm.trans (GaloisField.card 2 m mPos.ne')
  let FieldWitness (q : ℕ) : Prop := ∃ rows : Fin (width*q^2) → List (Fin (width*q^2)),
    Function.Injective rows ∧ (∀ i, (rows i).Nodup ∧ (rows i).length = width) ∧ BridgeFree (Before rows) 3 ∧
    (∑ i, (rows i).length) = (width*q^2)*width ∧
    (∀ x, (occurrences (fun i => (rows i).toFinset) x).card = width) ∧ listOutputAverageCaps rows
  have witness : FieldWitness (2^m) := card ▸ (show FieldWitness (Fintype.card K) from
    wenger_full_three_rows_on_width K (by omega) (card.symm ▸ widthFit))
  obtain ⟨rows,injective,lengths,free,mass,degree,_⟩ := witness
  have long (i : Fin v) : 2 ≤ (rows i).length := by rw [(lengths i).2]; omega
  have present (i : Fin v) : rows i ≠ [] ∧ (rows i).Nodup :=
    ⟨List.length_pos_iff.mp (lt_of_lt_of_le (by decide) (long i)),(lengths i).1⟩
  let copies := b/v
  have copiesFit : copies*v ≤ b := Nat.div_mul_le_self _ _
  have copiesPos : 1 ≤ copies := (Nat.le_div_iff_mul_le vPos).mpr (by simpa only [one_mul] using fit)
  have cover : b ≤ 2*(copies*v) := calc
    _ ≤ (copies+1)*v := by
      have gap := Nat.lt_mul_div_succ b vPos
      rw [Nat.mul_comm] at gap
      exact gap.le
    _ ≤ (2*copies)*v := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  obtain ⟨nCap,pCap⟩ := comparable_min_budget nClose pClose
  have spare : p-copies*v ≤ n := by
    rcases le_total p n with order | order
    · omega
    · have same : b = n := min_eq_left order
      rw [same] at cover
      omega
  obtain ⟨candidate,candidateDistinct,candidateRows,candidateFree,candidateMass⟩ :=
    exists_literal_full_disjoint_copies_with_singletons rows (fun i => (lengths i).1) long (by decide) free
      (copiesFit.trans bn) (copiesFit.trans bp) spare
  obtain ⟨paths,distinct,valid,half,maximal,_,_⟩ :=
    localOrderDistinctExtremal_isDense (k := 3) true hp
      ⟨candidate,candidateDistinct,candidateRows,candidateFree.halfFree⟩
  let M := ∑ i, (paths i).length
  have copiesLe : copies*(v*width) ≤ M := by
    rw [← mass]
    exact candidateMass.trans (maximal candidate candidateDistinct candidateRows candidateFree.halfFree)
  have upper : M ≤ 4*b*width := half_three_mass_le_four_min_width_of_comparable_budgets hn hp
    nClose pClose widthLarge cubic paths (fun i => (valid i).2) half le_rfl
  have retain : M ≤ 16*(∑ i, (rows i).length) := calc
    _ ≤ 4*b*width := upper
    _ ≤ 4*(4*v)*width := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 envelope)
    _ = _ := by rw [mass]; change _ = 16*(v*width); ring
  have witnessLe : (∑ i, (rows i).length) ≤ M := by
    rw [mass]
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < copies)).trans copiesLe
  have capsAt {budget : ℕ} (budgetPos : 0 < budget) (lo : b ≤ budget) (hi : 2*budget ≤ 3*b) :
      (M:ℝ)/(4*(budget:ℝ)) ≤ width ∧ (width:ℝ) ≤ 4*(M:ℝ)/budget := by
    have budgetBound : budget ≤ 4*(copies*v) := by omega
    have arithmetic : budget*width ≤ 4*M := calc
      _ ≤ (4*(copies*v))*width := Nat.mul_le_mul_right _ budgetBound
      _ = 4*(copies*(v*width)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ copiesLe
    have pos : (0:ℝ) < budget := Nat.cast_pos.mpr budgetPos
    have lowerR : (M:ℝ) ≤ 4*(budget:ℝ)*width := by
      exact_mod_cast upper.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 lo))
    have upperR : (budget:ℝ)*width ≤ 4*(M:ℝ) := by exact_mod_cast arithmetic
    refine ⟨(div_le_iff₀ (by positivity)).mpr ?_,(le_div_iff₀ pos).mpr ?_⟩
    · convert lowerR using 1
      ring
    · simpa only [mul_comm (width:ℝ)] using upperR
  have caps : frozenListCaps n p M rows := by
    simp only [frozenListCaps,degree,fun i => (lengths i).2]
    exact ⟨fun _ => capsAt hn bn nCap,fun _ => capsAt hp bp pCap⟩
  exact ⟨paths,distinct,valid,half,maximal,v,fit,rows,injective,present,free,witnessLe,retain,caps⟩

end OnlineReachabilityPreservers
