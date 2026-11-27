import Mathlib.Data.Fintype.Perm
import OnlineReachabilityPreservers.FrozenBoundaryCases
import OnlineReachabilityPreservers.OutputAverageDistinctCleaning

/-! Literal simple-path budgets below the first possible bridge size. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private abbrev SimpleRows (n : ℕ) := {row : List (Fin n) // row.Nodup}

private noncomputable def rowTailEquiv (n : ℕ) (head : Fin (n+1)) :
    Fin n ≃ {v : Fin (n+1) // v ≠ head} := by
  classical
  have card : Fintype.card {v : Fin (n+1) // v ≠ head} = n := by
    rw [Fintype.card_subtype_compl (fun v => v = head),Fintype.card_subtype_eq,Fintype.card_fin]
    omega
  exact (Fintype.equivFinOfCardEq card).symm

private noncomputable def encodeSimpleRow {n : ℕ} : SimpleRows (n+1) → Unit ⊕ (Fin (n+1) × SimpleRows n)
  | ⟨[],_⟩ => Sum.inl ()
  | ⟨x::tail,unique⟩ =>
    let labels := tail.attachWith (fun v => v ≠ x)
      (fun v on same => (List.nodup_cons.mp unique).1 (same ▸ on))
    have distinct : labels.Nodup := List.Nodup.of_map Subtype.val (by
      rw [List.attachWith_map_subtype_val]
      exact (List.nodup_cons.mp unique).2)
    Sum.inr (x,⟨labels.map (rowTailEquiv n x).symm,distinct.map (rowTailEquiv n x).symm.injective⟩)

private noncomputable def decodeSimpleRow {n : ℕ} : Unit ⊕ (Fin (n+1) × SimpleRows n) → List (Fin (n+1))
  | Sum.inl _ => []
  | Sum.inr (x,tail) => x :: tail.val.map (fun v => (rowTailEquiv n x v).val)

private theorem encodeSimpleRow_injective (n : ℕ) : Function.Injective (@encodeSimpleRow n) := by
  have exactRow (row : SimpleRows (n+1)) : decodeSimpleRow (encodeSimpleRow row) = row.val := by
    obtain ⟨row,unique⟩ := row
    cases row with
    | nil => rfl
    | cons head tail =>
      simp only [encodeSimpleRow,decodeSimpleRow,List.map_map,Function.comp_def,Equiv.apply_symm_apply,
        List.attachWith_map_subtype_val]
  intro a b same
  exact Subtype.ext ((exactRow a).symm.trans ((congrArg decodeSimpleRow same).trans (exactRow b)))

private theorem simpleRows_card_succ (n : ℕ) :
    Fintype.card (SimpleRows (n+1)) ≤ 1+(n+1)*Fintype.card (SimpleRows n) := by
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_unit,Fintype.card_fin] using
    Fintype.card_le_of_injective encodeSimpleRow (encodeSimpleRow_injective n)

private theorem simpleRows_card_zero : Fintype.card (SimpleRows 0) ≤ 1 := by
  have equal (a : SimpleRows 0) : a.val = [] := by
    obtain ⟨row,unique⟩ := a
    cases row with
    | nil => rfl
    | cons head _ => exact head.elim0
  have inj : Function.Injective (fun _ : SimpleRows 0 => ()) := fun a b _ => Subtype.ext ((equal a).trans (equal b).symm)
  simpa only [Fintype.card_unit] using Fintype.card_le_of_injective _ inj

/-- There are fewer than three times `n!` simple lists over `Fin n`,
including the empty list. -/
theorem simple_fin_lists_card_add_one_le_three_factorial (n : ℕ) :
    Fintype.card {row : List (Fin n) // row.Nodup}+1 ≤ 3*n.factorial := by
  change Fintype.card (SimpleRows n)+1 ≤ 3*n.factorial
  induction n with
  | zero =>
    rw [Nat.factorial_zero,Nat.mul_one]
    have := simpleRows_card_zero
    omega
  | succ n ih =>
    have count := simpleRows_card_succ n
    cases n with
    | zero =>
      have atOne : Fintype.card (SimpleRows 1) ≤ 1+Fintype.card (SimpleRows 0) := by simpa using count
      have atZero := simpleRows_card_zero
      change Fintype.card (SimpleRows 1)+1 ≤ 3
      omega
    | succ n =>
      rw [Nat.factorial_succ,← mul_assoc,Nat.mul_comm 3 (n+1+1),mul_assoc]
      have scale := Nat.mul_le_mul_left (n+1+1) ih
      rw [Nat.mul_add,Nat.mul_one] at scale
      omega

private abbrev NonemptySimpleRows (n : ℕ) := {row : SimpleRows n // row.val ≠ []}

private noncomputable def fullPermutationRow {n : ℕ} (hn : 0 < n) (perm : Equiv.Perm (Fin n)) :
    NonemptySimpleRows n :=
  ⟨⟨(List.finRange n).map perm,(List.nodup_finRange n).map perm.injective⟩,by
    intro empty
    have length := congrArg List.length empty
    simp only [List.length_map,List.length_finRange,List.length_nil] at length
    omega⟩

private theorem fullPermutationRow_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fullPermutationRow hn) := by
  intro a b same
  have lists : (List.finRange n).map a = (List.finRange n).map b :=
    congrArg (fun row : NonemptySimpleRows n => row.val.val) same
  apply Equiv.ext
  intro v
  have value := congrArg (fun l : List (Fin n) => l[v.val]?) lists
  have within : v.val < (List.finRange n).length := by simpa only [List.length_finRange] using v.isLt
  have index : Fin.cast List.length_finRange ⟨v.val,within⟩ = v := Fin.ext rfl
  simpa only [List.getElem?_map,List.getElem?_eq_getElem within,List.getElem_finRange,Option.map_some,Option.some.injEq,index] using value

private theorem permutationRow_length {n : ℕ} (hn : 0 < n) (perm : Equiv.Perm (Fin n)) :
    (fullPermutationRow hn perm).val.val.length = n := by simp [fullPermutationRow]

private theorem permutationRow_mem {n : ℕ} (hn : 0 < n) (perm : Equiv.Perm (Fin n)) (v : Fin n) :
    v ∈ (fullPermutationRow hn perm).val.val := by
  exact List.mem_map.mpr ⟨perm.symm v, List.mem_finRange _,perm.apply_symm_apply v⟩

private theorem admissible_of_cutoff_lt_two {V I : Type*} [DecidableEq V] [LinearOrder I]
    {k : ℕ} (small : k < 2) (half : Bool) (paths : I → List V) : localOrderAdmissible half k paths := by
  cases half <;> intro d bound <;> omega

/-- Below size two, a literal maximum at feasible positive budgets has
an at-most-budget witness of spanning permutations. It retains at least
one third of the maximum and meets both kinds of factor-four caps. -/
theorem localOrderDistinctExtremal_frozen_of_cutoff_lt_two {n p k : ℕ} (half : Bool)
    (small : k < 2) (hn : 0 < n) (hp : 0 < p)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ localOrderAdmissible half k paths) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ clean : Fin (min p n.factorial) → List (Fin n), Function.Injective clean ∧
        (∀ i, clean i ≠ [] ∧ (clean i).Nodup ∧ (clean i).length = n) ∧ localOrderAdmissible half k clean ∧
        M ≤ 3*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
        frozenListCaps n p M clean ∧ listOutputAverageCaps clean := by
  classical
  obtain ⟨paths,distinct,rows,allowed,maximal,_,_⟩ := localOrderDistinctExtremal_isDense half hp feasible
  let M := ∑ i, (paths i).length
  let Rows := NonemptySimpleRows n
  let given (i : Fin p) : Rows := ⟨⟨paths i,(rows i).2⟩,(rows i).1⟩
  have givenUnique : Function.Injective given := fun a b same => distinct (congrArg (fun row : Rows => row.val.val) same)
  have available : p ≤ Fintype.card Rows := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective given givenUnique
  have count : p ≤ 3*n.factorial := available.trans ((Fintype.card_le_of_injective
    (Subtype.val : Rows → SimpleRows n) Subtype.val_injective).trans (by
      have upper := simple_fin_lists_card_add_one_le_three_factorial n
      change Fintype.card (SimpleRows n)+1 ≤ 3*n.factorial at upper
      omega))
  let q := min p n.factorial
  have qLe : q ≤ p := min_le_left _ _
  have triples : p ≤ 3*q := by dsimp [q]; omega
  have permutations : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by simp [Fintype.card_perm]
  let perm (i : Fin q) := (Fintype.equivFinOfCardEq permutations).symm (Fin.castLE (min_le_right _ _) i)
  have permUnique : Function.Injective perm := (Fintype.equivFinOfCardEq permutations).symm.injective.comp (Fin.castLE_injective _)
  let base (i : Fin q) : Rows := fullPermutationRow hn (perm i)
  have baseUnique : Function.Injective base := (fullPermutationRow_injective hn).comp permUnique
  let wanted := (univ : Finset (Fin q)).image base
  have wantedCard : wanted.card = q := by
    rw [show wanted = univ.image base from rfl,card_image_of_injective _ baseUnique,card_univ,Fintype.card_fin]
  obtain ⟨extended,contains,_,exactCount⟩ := exists_subsuperset_card_eq (subset_univ wanted)
    (wantedCard ▸ qLe) (by simpa only [card_univ] using available)
  let order := (Fintype.equivFinOfCardEq ((Fintype.card_coe extended).trans exactCount)).symm
  let extendedPaths (i : Fin p) := (order i).val.val.val
  have extendedRows (i : Fin p) : extendedPaths i ≠ [] ∧ (extendedPaths i).Nodup :=
    ⟨(order i).val.property,(order i).val.val.property⟩
  have extendedUnique : Function.Injective extendedPaths :=
    Subtype.val_injective.comp (Subtype.val_injective.comp (Subtype.val_injective.comp order.injective))
  have baseMass (i : Fin q) : (base i).val.val.length = n := permutationRow_length hn (perm i)
  have expandedMass : (∑ i, (extendedPaths i).length) = ∑ row ∈ extended, row.val.val.length :=
    (Equiv.sum_comp order (fun row : extended => row.val.val.val.length)).trans
      (extended.sum_coe_sort (fun row => row.val.val.length))
  have initialMass : (∑ row ∈ wanted, row.val.val.length) = q*n := by
    rw [show wanted = univ.image base from rfl,sum_image (fun _ _ _ _ equal => baseUnique equal)]
    simp only [baseMass,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  have lower : q*n ≤ M := calc
    _ = ∑ row ∈ wanted, row.val.val.length := initialMass.symm
    _ ≤ ∑ row ∈ extended, row.val.val.length := sum_le_sum_of_subset_of_nonneg contains (fun _ _ _ => Nat.zero_le _)
    _ = ∑ i, (extendedPaths i).length := expandedMass.symm
    _ ≤ M := maximal extendedPaths extendedUnique extendedRows (admissible_of_cutoff_lt_two small half extendedPaths)
  have upper : M ≤ p*n := by
    calc
      _ ≤ ∑ _ : Fin p, n := sum_le_sum fun i _ => by
        rw [← List.toFinset_card_of_nodup (rows i).2]
        simpa only [card_univ,Fintype.card_fin] using card_le_univ (paths i).toFinset
      _ = _ := by simp
  have threeMass : M ≤ 3*(q*n) := upper.trans (by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right n triples)
  let clean (i : Fin q) := (base i).val.val
  have cleanSimple (i : Fin q) : (clean i).Nodup := (base i).val.property
  have cleanDegree (v : Fin n) : (occurrences (fun i => (clean i).toFinset) v).card = q := by
    have every : occurrences (fun i => (clean i).toFinset) v = univ := by
      ext i
      simp only [mem_occurrences,mem_univ,iff_true,List.mem_toFinset]
      exact permutationRow_mem hn (perm i) v
    rw [every,card_univ,Fintype.card_fin]
  have cleanMass : (∑ i, (clean i).length) = q*n := by
    simp only [show ∀ i, (clean i).length = n from baseMass,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  refine ⟨paths,distinct,rows,allowed,maximal,clean,
    Subtype.val_injective.comp (Subtype.val_injective.comp baseUnique),
    fun i => ⟨(base i).property,cleanSimple i,baseMass i⟩,admissible_of_cutoff_lt_two small half clean,?_,?_,?_,?_⟩
  · rwa [cleanMass]
  · rwa [cleanMass]
  · have nPos : (0:ℝ) < n := by exact_mod_cast hn
    have pPos : (0:ℝ) < p := by exact_mod_cast hp
    have q0 : (0:ℝ) ≤ q := by positivity
    have m0 : (0:ℝ) ≤ M := by positivity
    have minimum : (q:ℝ)*n ≤ M := by exact_mod_cast lower
    have maximum : (M:ℝ) ≤ (p:ℝ)*n := by exact_mod_cast upper
    have witness : (M:ℝ) ≤ 3*((q:ℝ)*n) := by exact_mod_cast threeMass
    have allRows : (p:ℝ) ≤ 3*(q:ℝ) := by exact_mod_cast triples
    refine ⟨?_,?_⟩
    · intro v
      rw [cleanDegree]
      exact ⟨(div_le_iff₀ (by positivity)).mpr (by nlinarith),
        (le_div_iff₀ nPos).mpr (by linarith)⟩
    · intro i
      rw [show (clean i).length = n from baseMass i]
      exact ⟨(div_le_iff₀ (by positivity)).mpr (by nlinarith),
        (le_div_iff₀ pPos).mpr (by nlinarith)⟩
  · apply listOutputAverageCaps_of_widths clean cleanSimple q n
    · intro v
      rw [cleanDegree]
      exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) q],le_rfl⟩
    · intro i
      rw [show (clean i).length = n from baseMass i]
      exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) n],le_rfl⟩

end OnlineReachabilityPreservers
