import OnlineReachabilityPreservers.DistinctPathBudgets
import OnlineReachabilityPreservers.HalfFiveAverageCleaning
import OnlineReachabilityPreservers.LocalFrozenLowMass

/-! Transfer output-average cleaning to literal sets of distinct simple paths. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

private theorem outputAverageCaps_of_uniform {V I : Type*} [DecidableEq V] [Fintype V] [Fintype I]
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup) {d l : ℕ}
    (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card = d)
    (length : ∀ i, (paths i).length = l) : listOutputAverageCaps paths := by
  let M := ∑ i, (paths i).length
  have degreeMass : M = Fintype.card V*d := by
    calc
      _ = ∑ i, (paths i).toFinset.card := sum_congr rfl
        (fun i _ => (List.toFinset_card_of_nodup (simple i)).symm)
      _ = ∑ v, (occurrences (fun i => (paths i).toFinset) v).card :=
        (sum_occurrences (fun i => (paths i).toFinset)).symm
      _ = _ := by simp [degree,Nat.mul_comm]
  have lengthMass : M = Fintype.card I*l := by simp [M,length,Nat.mul_comm]
  constructor
  · intro v
    have count : ((Fintype.card V : ℕ):ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨v⟩).ne'
    have avg : (M:ℝ)/Fintype.card V = d := by
      rw [degreeMass,Nat.cast_mul,mul_comm,mul_div_cancel_right₀ _ count]
    change ((M:ℝ)/Fintype.card V)/4 ≤ _ ∧ _ ≤ 4*((M:ℝ)/Fintype.card V)
    rw [avg,degree]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) d]
  · intro i
    have count : ((Fintype.card I : ℕ):ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
    have avg : (M:ℝ)/Fintype.card I = l := by
      rw [lengthMass,Nat.cast_mul,mul_comm,mul_div_cancel_right₀ _ count]
    change ((M:ℝ)/Fintype.card I)/4 ≤ _ ∧ _ ≤ 4*((M:ℝ)/Fintype.card I)
    rw [avg,length]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) l]

private theorem outputAverage_distinct_sparse {n p M k : ℕ}
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (enoughPairs : p ≤ n*n) (sparse : M ≤ 1568*p) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 7056*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      listOutputAverageCaps clean := by
  by_cases order : p ≤ n
  · let clean : Fin 1 → List (Fin n) := fun _ => List.finRange n
    have nonempty (i : Fin 1) : clean i ≠ [] := fun empty => by
      have len := congrArg List.length empty
      simp [clean] at len
      omega
    have degree (v : Fin n) : (occurrences (fun i => (clean i).toFinset) v).card = 1 := by
      simp [occurrences,clean]
    have length (i : Fin 1) : (clean i).length = n := List.length_finRange
    have simple (i : Fin 1) : (clean i).Nodup := List.nodup_finRange n
    have free : BridgeFree (Before clean) k :=
      fun _ _ => ⟨fun b => b.river_ne_arc 0 (Subsingleton.elim _ _)⟩
    have mass : (∑ i : Fin 1, (clean i).length) = n := by simp [length]
    exact ⟨n,le_rfl,1,hp,clean,(fun _ _ _ => Subsingleton.elim _ _),nonempty,simple,free,
      (by rw [mass]; omega),(by rw [mass]; exact dense),outputAverageCaps_of_uniform clean simple degree length⟩
  have twoN : 2 ≤ n := by
    by_contra! tooSmall
    have one : n = 1 := by omega
    simp [one] at enoughPairs
    omega
  let a := n/2
  let b := (p/2).sqrt
  let w := min a b
  have aPos : 0 < a := by dsimp [a]; omega
  have bPos : 0 < b := Nat.sqrt_pos.mpr (by omega)
  have byN : 2*w ≤ n := calc
    _ ≤ 2*a := Nat.mul_le_mul_left _ (min_le_left _ _)
    _ ≤ n := by dsimp [a]; omega
  have byP : w*w ≤ p/2 := (Nat.mul_le_mul (min_le_right _ _) (min_le_right _ _)).trans (Nat.sqrt_le _)
  have capacityA : p ≤ 9*(a*a) := calc
    _ ≤ n^2 := by simpa only [pow_two] using enoughPairs
    _ ≤ (3*a)^2 := Nat.pow_le_pow_left (by dsimp [a]; omega) 2
    _ = _ := by ring
  have capacityB : p ≤ 9*(b*b) := by
    have bound : p/2 < 4*(b*b) := calc
      _ < (b+1)^2 := Nat.lt_succ_sqrt' _
      _ ≤ (2*b)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
    have one : 1 ≤ b*b := Nat.mul_pos bPos bPos
    omega
  have capacity : p ≤ 9*(w*w) := by
    rcases le_total a b with ab | ba
    · simpa only [w,min_eq_left ab] using capacityA
    · simpa only [w,min_eq_right ba] using capacityB
  let clean := frozenRectangleRows 1 w
  have length (i : Fin (1*(w*w))) : (clean i).length = 2 := by simp [clean,frozenRectangleRows]
  have simple (i : Fin (1*(w*w))) : (clean i).Nodup := frozenRectangleRows_simple i
  have uniform (v : Fin (1*(2*w))) : (occurrences (fun i => (clean i).toFinset) v).card = w :=
    frozenRectangleRows_degree 1 w v
  have free := frozenRectangleRows_free 1 w (max 2 k)
  have injective : Function.Injective clean :=
    nontrivial_halfFree_paths_injective simple (fun i => (length i).ge) (le_max_left _ _) free.halfFree
  have nonempty (i : Fin (1*(w*w))) : clean i ≠ [] := by
    intro empty
    have len := length i
    rw [empty,List.length_nil] at len
    exact Nat.noConfusion len
  have mass : (∑ i : Fin (1*(w*w)), (clean i).length) = 2*(w*w) := by simp [length,Nat.mul_comm]
  refine ⟨_,by simpa only [one_mul] using byN,_,by simp only [one_mul]; omega,clean,injective,nonempty,
    simple,(fun _ small => free (small.trans (le_max_right _ _))),?_,?_,
    outputAverageCaps_of_uniform clean simple uniform length⟩
  · rw [mass]
    omega
  · rw [mass]
    omega

/-- Transfer a factor-four output-average witness to distinct nonempty
paths. A witness containing a row of length at most one has small enough
total mass to use a single spanning path or a uniform length-two family. -/
theorem regularization_list_output_average_distinct_of_indexed {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    (indexed : p ≤ ∑ i, (paths i).length →
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      (∑ i, (paths i).length) ≤ 7056*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  let M := ∑ i, (paths i).length
  have long : p ≤ M := by
    calc
      _ = ∑ i : Fin p, (1:ℕ) := by simp
      _ ≤ _ := sum_le_sum fun i _ => List.length_pos_of_ne_nil (nonempty i)
  have halfFromAllowed {v q : ℕ} {family : Fin q → List (Fin v)}
      (legal : localOrderAdmissible half k family) : HalfBridgeFree (Before family) k := by
    cases half
    · exact (show BridgeFree (Before family) k from legal).halfFree
    · exact legal
  obtain ⟨v,vCap,q,qCap,clean,cleanSimple,cleanAllowed,mass,upper,caps⟩ := indexed long
  by_cases enough : ∀ i, 2 ≤ (clean i).length
  · have injective := nontrivial_halfFree_paths_injective cleanSimple enough two (halfFromAllowed cleanAllowed)
    have present (i : Fin q) : clean i ≠ [] := fun empty => by
      have positive := enough i
      rw [empty,List.length_nil] at positive
      omega
    exact ⟨v,vCap,q,qCap,clean,injective,present,cleanSimple,cleanAllowed,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  push Not at enough
  obtain ⟨i,small⟩ := enough
  let K := ∑ j, (clean j).length
  have qPos : 0 < (q:ℝ) := by exact_mod_cast (Nat.zero_le i.val).trans_lt i.isLt
  have lower := (caps.2 i).1
  change ((K:ℝ)/(Fintype.card (Fin q):ℝ))/4 ≤ ((clean i).length:ℝ) at lower
  rw [Fintype.card_fin] at lower
  have len : ((clean i).length:ℝ) ≤ 1 := by exact_mod_cast (show (clean i).length ≤ 1 by omega)
  have avg : (K:ℝ)/(q:ℝ) ≤ 4 := by linarith
  have kSmall : K ≤ 4*q := by exact_mod_cast (div_le_iff₀ qPos).mp avg
  have mSmall : M ≤ 1568*p := by
    change M ≤ 392*K at mass
    omega
  have pCap := distinctPathCount_le_square paths distinct nonempty simple two (halfFromAllowed allowed)
  obtain ⟨v',vFits,q',qFits,witness,witnessDistinct,witnessPresent,witnessSimple,witnessFree,witnessMass,
    witnessUpper,witnessCaps⟩ := outputAverage_distinct_sparse hn hp dense long
      (by simpa only [pow_two] using pCap) mSmall (k := k)
  have witnessAllowed : localOrderAdmissible half k witness := by cases half; exacts [witnessFree,witnessFree.halfFree]
  exact ⟨v',vFits,q',qFits,witness,witnessDistinct,witnessPresent,witnessSimple,witnessAllowed,
    witnessMass,witnessUpper,witnessCaps⟩

/-- Half-five cleaning with output-average caps for a literal path set. -/
theorem regularization_list_output_average_half_five_distinct {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (rows : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      (∑ i, (paths i).length) ≤ 7056*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨v,vFits,q,qFits,clean,injective,nonempty,simple,legal,mass,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed (half := true)
      paths distinct (fun i => (rows i).1) (fun i => (rows i).2) allowed (by decide) hn hp dense
      (regularization_list_output_average_half_five paths (fun i => (rows i).2) allowed hn hp dense)
  exact ⟨v,vFits,q,qFits,clean,injective,fun i => ⟨nonempty i,simple i⟩,legal,mass,upper,caps⟩

/-- If a literal system with exactly the original path budget exists, its
half-five maximum has an output-average witness within both original budgets. -/
theorem localOrderDistinctExtremal_output_average_half_five {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 5) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 5 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 5 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
        (∑ i, (paths i).length) ≤ 7056*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,distinct,rows,allowed,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense true hp feasible
  exact ⟨paths,distinct,rows,allowed,maximal,
    regularization_list_output_average_half_five_distinct paths distinct rows allowed hn hp dense⟩

/-- Full-six cleaning with output-average caps for a literal path set. -/
theorem regularization_list_output_average_full_six_distinct {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (rows : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : BridgeFree (Before paths) 6) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ BridgeFree (Before clean) 6 ∧
      (∑ i, (paths i).length) ≤ 7056*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨v,vFits,q,qFits,clean,injective,nonempty,simple,legal,mass,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed (half := false)
      paths distinct (fun i => (rows i).1) (fun i => (rows i).2) allowed (by decide) hn hp dense
      (regularization_list_output_average_six paths (fun i => (rows i).2) false allowed (by simp) hn hp dense)
  exact ⟨v,vFits,q,qFits,clean,injective,fun i => ⟨nonempty i,simple i⟩,legal,mass,upper,caps⟩

/-- If a literal system with exactly the original path budget exists, its
full-six maximum has an output-average witness within both original budgets. -/
theorem localOrderDistinctExtremal_output_average_full_six {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) 6) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) 6 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (Before other) 6 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ BridgeFree (Before clean) 6 ∧
        (∑ i, (paths i).length) ≤ 7056*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,distinct,rows,allowed,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense false hp feasible
  exact ⟨paths,distinct,rows,allowed,maximal,
    regularization_list_output_average_full_six_distinct paths distinct rows allowed hn hp dense⟩

/-- Cutoff-four cleaning with output-average caps for a literal path set. -/
theorem regularization_list_output_average_four_distinct {n p : ℕ}
    (half : Bool) (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (rows : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half 4 paths) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ localOrderAdmissible half 4 clean ∧
      (∑ i, (paths i).length) ≤ 7056*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨v,vFits,q,qFits,clean,injective,nonempty,simple,legal,mass,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed (half := half)
      paths distinct (fun i => (rows i).1) (fun i => (rows i).2) allowed (by decide) hn hp dense
      (regularization_list_output_average_four paths (fun i => (rows i).2) half allowed hn hp dense)
  exact ⟨v,vFits,q,qFits,clean,injective,fun i => ⟨nonempty i,simple i⟩,legal,mass,upper,caps⟩

/-- If a literal system with exactly the original path budget exists, its
cutoff-four maximum has an output-average witness within both original budgets. -/
theorem localOrderDistinctExtremal_output_average_four {n p : ℕ} (half : Bool) (hn : 0 < n) (hp : 0 < p)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ localOrderAdmissible half 4 paths) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ localOrderAdmissible half 4 paths ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → localOrderAdmissible half 4 other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ localOrderAdmissible half 4 clean ∧
        (∑ i, (paths i).length) ≤ 7056*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,distinct,rows,allowed,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense half hp feasible
  exact ⟨paths,distinct,rows,allowed,maximal,
    regularization_list_output_average_four_distinct half paths distinct rows allowed hn hp dense⟩

end OnlineReachabilityPreservers
