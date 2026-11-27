import OnlineReachabilityPreservers.FrozenWengerThree
import OnlineReachabilityPreservers.ExtremalCopyBounds

/-! The literal frozen full-three witness for sufficiently large equal budgets. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private theorem full_family_replace_short_by_singletons {n p k : ℕ} (budget : p ≤ n) (two : 2 ≤ k)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) :
    ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧
      BridgeFree (Before rows) k ∧ (∑ i, (paths i).length) ≤ ∑ i, (rows i).length := by
  let rows (i : Fin p) := if 2 ≤ (paths i).length then paths i else [Fin.castLE budget i]
  have longUnique {i j : Fin p} (iLong : 2 ≤ (paths i).length) (same : paths i = paths j) : i = j := by
    by_contra different
    let a := (paths i)[0]'(by omega)
    let b := (paths i)[1]'(by omega)
    have step : Before paths i a b := by
      refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
      dsimp only [a,b]
      rw [(simple i).idxOf_getElem,(simple i).idxOf_getElem]
      decide
    have parallel : Before paths j a b := by
      unfold SourceAudit.BeforeIn at step ⊢
      rw [← same]
      exact step
    exact no_parallel_list_steps free.halfFree two different step parallel
  refine ⟨rows,?_,?_,?_,?_⟩
  · intro i j equal
    by_cases iLong : 2 ≤ (paths i).length <;> by_cases jLong : 2 ≤ (paths j).length
    · exact longUnique iLong (by simpa [rows,iLong,jLong] using equal)
    · have values := congrArg List.length equal
      simp [rows,iLong,jLong] at values
      omega
    · have values := congrArg List.length equal
      simp [rows,iLong,jLong] at values
      omega
    · exact Fin.castLE_injective budget (by simpa [rows,iLong,jLong] using equal)
  · intro i
    by_cases long : 2 ≤ (paths i).length
    · rw [show rows i = paths i from ite_eq_left long]
      exact ⟨List.length_pos_iff.mp (by omega),simple i⟩
    · simp [rows,long]
  · have inherits {i x y} (step : Before rows i x y) : Before paths i x y := by
      by_cases long : 2 ≤ (paths i).length
      · simpa only [SourceAudit.BeforeIn,rows,ite_eq_left long] using step
      · have absolute := listBefore_ne step
        have left : x = Fin.castLE budget i := by simpa [rows,long] using step.1
        have right : y = Fin.castLE budget i := by simpa [rows,long] using step.2.1
        exact (absolute (left.trans right.symm)).elim
    intro d bound
    exact ⟨fun b => (free bound).false (b.mapPaths id Function.injective_id (fun _ _ _ step => inherits step))⟩
  · apply sum_le_sum
    intro i _
    by_cases long : 2 ≤ (paths i).length
    · simp [rows,long]
    · simp [rows,long]
      omega

/-- At equal budgets and field scale `q` of at least 256, the latest-hit
bound controls half mass at `4 n q` when `n < 8 q³`. -/
theorem half_three_mass_le_four_nq_of_equal_large_budget {n q k : ℕ}
    (positive : 0 < n) (large : 256 ≤ q) (upper : n < 8*q^3)
    (paths : Fin n → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) : (∑ i, (paths i).length) ≤ 4*n*q := by
  let M := ∑ i, (paths i).length
  let S := M-M/16-17*n
  have bound := half_three_latest_intersection_shifted_mass_cube_le positive positive paths simple half three 15
  have cube : S^3 ≤ 6*(n*n)^2 := by
    change (M-M/16-(16*n+n))^3 ≤ _ at bound
    have same : 16*n+n = 17*n := by ring
    simpa only [S,same] using bound
  by_contra! excess
  change 4*n*q < M at excess
  have scale : 204*n ≤ n*q := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left n (show 204 ≤ q by omega)
  have floor : 16*(M/16) ≤ M := Nat.mul_div_le _ _
  have gap : 11*(n*q) < 3*S := by dsimp only [S]; rw [show 4*n*q = 4*(n*q) by ring] at excess; omega
  have cap : (3*S)^3 ≤ 1296*(n*q)^3 := calc
    _ = 27*S^3 := by ring
    _ ≤ 27*(6*(n*n)^2) := Nat.mul_le_mul_left _ cube
    _ = 162*(n*n^3) := by ring
    _ ≤ 162*((8*q^3)*n^3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ upper.le)
    _ = _ := by ring
  have last : 1296*(n*q)^3 ≤ (11*(n*q))^3 := by
    calc
      _ ≤ 1331*(n*q)^3 := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by ring
  exact (not_lt_of_ge (cap.trans last)) (pow_lt_pow_left₀ gap (Nat.zero_le _) (by decide : 3 ≠ 0))

/-- For equal budgets at least `256³`, the literal half maximum at
cutoff three exists and a full-three witness within both budgets keeps
at least one thirty-second of it with the four starting-average caps. -/
theorem localOrderDistinctExtremal_frozen_full_three_at_equal_large_budgets {n : ℕ}
    (large : 256^3 ≤ n) :
    ∃ paths : Fin n → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin n → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ q : ℕ, q^3 ≤ n ∧ ∃ rows : Fin (q^3) → List (Fin (q^3)),
        Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) = q^4 ∧ (∑ i, (rows i).length) ≤ M ∧ M ≤ 32*(∑ i, (rows i).length) ∧
        frozenListCaps n n M rows := by
  let m := Nat.log 8 n
  let q := 2^m
  have hn : 0 < n := Nat.lt_of_lt_of_le (by decide) large
  have size : 8 ≤ m := Nat.le_log_of_pow_le (by decide) (by exact large)
  have largeQ : 256 ≤ q := Nat.pow_le_pow_right (by decide : 0 < 2) size
  have qPos : 0 < q := by omega
  have cubePower : q^3 = 8^m := by dsimp only [q]; rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have fit : q^3 ≤ n := cubePower.trans_le (Nat.pow_log_le_self 8 hn.ne')
  have envelope : n < 8*q^3 := by
    have high := Nat.lt_pow_succ_log_self (by decide : 1 < 8) n
    calc
      _ < 8^(m+1) := high
      _ = _ := by rw [cubePower,pow_succ,Nat.mul_comm]
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let K := GaloisField 2 m
  let : Fintype K := Fintype.ofFinite K
  have card : Fintype.card K = q := (Nat.card_eq_fintype_card).symm.trans (GaloisField.card 2 m (by omega))
  let FieldWitness (r : ℕ) : Prop := ∃ rows : Fin (r^3) → List (Fin (r^3)), Function.Injective rows ∧
    (∀ i, (rows i).Nodup ∧ (rows i).length = r) ∧ BridgeFree (Before rows) 3 ∧
    (∑ i, (rows i).length) = r^4 ∧ (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = r) ∧
    listOutputAverageCaps rows
  have fieldWitness : FieldWitness q := card ▸ (show FieldWitness (Fintype.card K) from wenger_full_three_rows K)
  obtain ⟨rows,injective,lengths,free,mass,degree,_⟩ := fieldWitness
  have present (i : Fin (q^3)) : rows i ≠ [] ∧ (rows i).Nodup := by
    refine ⟨fun empty => ?_,(lengths i).1⟩
    have width := (lengths i).2
    rw [empty,List.length_nil] at width
    exact (Nat.ne_of_gt qPos) width.symm
  let copies := if n ≤ 4*q^3 then 1 else 2
  have copiesFit : copies*q^3 ≤ n := by
    dsimp only [copies]
    split
    · simpa using fit
    · omega
  have copiesPos : 1 ≤ copies := by dsimp only [copies]; split <;> decide
  have copiesMass : n*q ≤ 4*(copies*q^4) := by
    dsimp only [copies]
    split
    · next bound =>
        calc
          _ ≤ (4*q^3)*q := Nat.mul_le_mul_right _ bound
          _ = _ := by ring
    · calc
        _ ≤ (8*q^3)*q := Nat.mul_le_mul_right _ envelope.le
        _ = _ := by ring
  obtain ⟨padded,paddedSimple,paddedFree,paddedMass⟩ := exists_disjoint_copies_with_budgets
    (half := false) rows (fun i => (lengths i).1) free copiesFit copiesFit
  obtain ⟨candidate,candidateDistinct,candidateRows,candidateFree,candidateMass⟩ :=
    full_family_replace_short_by_singletons le_rfl (by decide : 2 ≤ 3) padded paddedSimple paddedFree
  obtain ⟨paths,distinct,valid,half,maximal,_,_⟩ := localOrderDistinctExtremal_isDense (k := 3) true hn
    ⟨candidate,candidateDistinct,candidateRows,candidateFree.halfFree⟩
  let M := ∑ i, (paths i).length
  have candidateLe : (∑ i, (candidate i).length) ≤ M :=
    maximal candidate candidateDistinct candidateRows candidateFree.halfFree
  have witnessLe : q^4 ≤ M := calc
    _ ≤ copies*q^4 := Nat.le_mul_of_pos_left _ (by omega)
    _ = ∑ i, (padded i).length := by rw [paddedMass,mass]
    _ ≤ _ := candidateMass.trans candidateLe
  have volume : n*q ≤ 4*M := copiesMass.trans
    (Nat.mul_le_mul_left _ (by rw [← mass,← paddedMass]; exact candidateMass.trans candidateLe))
  have upper := half_three_mass_le_four_nq_of_equal_large_budget hn largeQ envelope paths
    (fun i => (valid i).2) half le_rfl
  have retain : M ≤ 32*q^4 := calc
    _ ≤ 4*n*q := upper
    _ ≤ 4*(8*q^3)*q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ envelope.le)
    _ = _ := by ring
  have nPos : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have lowerCap : (M:ℝ)/(4*(n:ℝ)) ≤ q := by
    apply (div_le_iff₀ (by positivity)).mpr
    have arithmetic : (M:ℝ) ≤ 4*(n:ℝ)*q := by exact_mod_cast upper
    convert arithmetic using 1
    ring
  have upperCap : (q:ℝ) ≤ 4*(M:ℝ)/n := by
    apply (le_div_iff₀ nPos).mpr
    simpa only [mul_comm (q:ℝ)] using (show (n:ℝ)*q ≤ 4*(M:ℝ) by exact_mod_cast volume)
  have caps : frozenListCaps n n M rows := by
    simp only [frozenListCaps,degree,fun i => (lengths i).2]
    exact ⟨fun _ => ⟨lowerCap,upperCap⟩,fun _ => ⟨lowerCap,upperCap⟩⟩
  exact ⟨paths,distinct,valid,half,maximal,q,fit,rows,injective,present,free,mass,
    mass.trans_le witnessLe,by rw [mass]; exact retain,caps⟩

end OnlineReachabilityPreservers
