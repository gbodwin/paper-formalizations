import OnlineReachabilityPreservers.FullBridgeCleaning

/-! Empty budgets, short cutoffs, and cutoffs covering all possible bridge sizes. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

/-- A bridge needs as many distinct rows as distinct vertices. -/
theorem bridge_size_le_both_budgets {n p r : ℕ} {before : Fin p → Fin n → Fin n → Prop}
    (b : Bridge before r) : r+2 ≤ min n p := by
  apply le_min
  · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective b.vertex b.distinctVertices
  · simpa only [Fintype.card_fin] using SourceAudit.bridge_path_count_le b

/-- A cutoff covering either entire budget excludes every full bridge. -/
theorem bridgeFree_all_of_cutoff_ge_min {n p k : ℕ} {before : Fin p → Fin n → Fin n → Prop}
    (free : BridgeFree before k) (large : min n p ≤ k) (r : ℕ) : IsEmpty (Bridge before r) :=
  ⟨fun b => (free ((bridge_size_le_both_budgets b).trans large)).false b⟩

/-- A finite cutoff covering either budget gives the all-size frozen full
cleaning result at the unrestricted maximum. -/
theorem localOrderExtremal_frozen_full_of_cutoff_ge_min (n p k : ℕ) (hn : 0 < n) (hp : 0 < p)
    (large : min n p ≤ k) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (Before paths) k ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) k →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ (∀ r, IsEmpty (Bridge (Before clean) r)) ∧
        M ≤ 40*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p k false hn hp
  exact ⟨paths,simple,free,maximal,
    regularization_list_frozen_full_all paths simple (bridgeFree_all_of_cutoff_ge_min free large)
      hn hp dense long⟩

/-- Through size three, the unrestricted maximum has a frozen-cap witness
with both budgets, while keeping the requested bridge exclusion. -/
theorem localOrderExtremal_frozen_short (n p k : ℕ) (half : Bool) (hn : 0 < n) (hp : 0 < p)
    (short : k ≤ 3) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,allowed,maximal,A,B,sizeA,sizeB,legal,retained,upper,deg,len⟩ :=
    localOrderExtremal_balanced_short n p half short hn hp
  let M := ∑ i, (paths i).length
  let D := (4*M)/Fintype.card (Fin n)
  let L := (4*M)/Fintype.card (Fin p)
  let pieces := listRegularizedPaths paths D L
  let clean := restrictListPaths pieces A B
  have cleanSimple (i : B) : (clean i).Nodup :=
    restrictListPath_nodup (listRegularizedPaths_simple paths simple D L i.val) A
  obtain ⟨finiteSimple,finiteLegal,mass,degree,length⟩ := relabelListPathsFin_spec clean cleanSimple legal
  refine ⟨paths,simple,allowed,maximal,Fintype.card (↥A),?_,Fintype.card (↥B),?_,
    relabelListPathsFin clean,finiteSimple,finiteLegal,?_,?_,?_,?_⟩
  · simpa only [Fintype.card_coe] using sizeA
  · simpa only [Fintype.card_coe] using sizeB
  · rw [mass]
    exact retained
  · rw [mass]
    exact upper
  · intro v
    rw [degree]
    exact deg _
  · intro i
    rw [length]
    exact len _

/-- Either an empty budget or a cutoff below two permits the maximal
constant list family. No incidence loss is required. -/
theorem localOrderExtremal_frozen_empty_or_cutoff_small (n p k : ℕ) (half : Bool)
    (trivial : n = 0 ∨ p = 0 ∨ k ≤ 1) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      (∑ i, (paths i).length) = p*n ∧ frozenListCaps n p (∑ i, (paths i).length) paths := by
  let paths (_ : Fin p) := List.finRange n
  have allowed : localOrderAdmissible half k paths := by
    have noBridge {r} (size : r+2 ≤ k) (b : Bridge (Before paths) r) : False := by
      have limit := bridge_size_le_both_budgets b
      have v := limit.trans (min_le_left n p)
      have j := limit.trans (min_le_right n p)
      rcases trivial with empty | empty | small
      · omega
      · omega
      · omega
    cases half
    · exact fun _ size => ⟨noBridge size⟩
    · exact fun _ size b _ => noBridge size b
  have actual : (∑ i, (paths i).length) = p*n := by simp [paths]
  have everyVertex (v : Fin n) : (occurrences (fun i => (paths i).toFinset) v).card = p := by
    have all : occurrences (fun i => (paths i).toFinset) v = univ := by
      ext i
      simp [mem_occurrences,paths]
    rw [all,card_univ,Fintype.card_fin]
  refine ⟨paths,fun _ => List.nodup_finRange _,allowed,?_,actual,?_,?_⟩
  · intro other simple _
    rw [actual]
    calc
      _ ≤ ∑ _ : Fin p, n := sum_le_sum fun i _ => by
        rw [← List.toFinset_card_of_nodup (simple i)]
        simpa only [Fintype.card_fin] using (Finset.card_le_univ (other i).toFinset)
      _ = _ := by simp
  · intro v
    rw [actual,everyVertex]
    have nPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt v.isLt)
    push_cast
    constructor
    · apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
      nlinarith only [mul_nonneg (show (0:ℝ) ≤ p by positivity) nPos.le]
    · apply (le_div_iff₀ nPos).mpr
      nlinarith only [mul_nonneg (show (0:ℝ) ≤ p by positivity) nPos.le]
  · intro i
    rw [actual]
    simp only [paths,List.length_finRange]
    have pPos : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
    push_cast
    constructor
    · apply (div_le_iff₀ (by positivity : 0 < 4*(p:ℝ))).mpr
      nlinarith only [mul_nonneg (show (0:ℝ) ≤ n by positivity) pPos.le]
    · apply (le_div_iff₀ pPos).mpr
      nlinarith only [mul_nonneg (show (0:ℝ) ≤ n by positivity) pPos.le]

end OnlineReachabilityPreservers
