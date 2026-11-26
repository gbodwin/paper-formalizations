import OnlineReachabilityPreservers.LocalFrozenLowMass
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Count all ordered pairs on simple paths and apply the low-mass cleaning. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private def forwardVertexPairs {n : ℕ} (path : List (Fin n)) : Finset (Fin n × Fin n) :=
  path.toFinset.offDiag.filter fun e => path.idxOf e.1 < path.idxOf e.2

private theorem forwardVertexPairs_before {n p : ℕ} {paths : Fin p → List (Fin n)} {i : Fin p}
    {e : Fin n × Fin n} (member : e ∈ forwardVertexPairs (paths i)) : ListBefore paths i e.1 e.2 := by
  obtain ⟨inside,ordered⟩ := mem_filter.mp member
  obtain ⟨first,second,_⟩ := mem_offDiag.mp inside
  exact ⟨List.mem_toFinset.mp first,List.mem_toFinset.mp second,ordered⟩

private theorem forwardVertexPairs_twice {n : ℕ} (path : List (Fin n)) (simple : path.Nodup) :
    2*(forwardVertexPairs path).card+path.length = path.length^2 := by
  let all := path.toFinset.offDiag
  let fwd := forwardVertexPairs path
  let bwd := all.filter fun e => path.idxOf e.2 < path.idxOf e.1
  have disjoint : Disjoint fwd bwd := by
    rw [disjoint_left]
    intro e earlier later
    exact lt_asymm (mem_filter.mp earlier).2 (mem_filter.mp later).2
  have covers : fwd ∪ bwd = all := by
    ext e
    constructor
    · intro member
      rcases mem_union.mp member with direct | reverse
      · exact (mem_filter.mp direct).1
      · exact (mem_filter.mp reverse).1
    · intro member
      obtain ⟨u,v,different⟩ := mem_offDiag.mp member
      have total := listBefore_total (paths := fun _ : Unit => path) (i := ())
        (List.mem_toFinset.mp u) (List.mem_toFinset.mp v) different
      rcases total with earlier | later
      · exact mem_union_left _ (mem_filter.mpr ⟨member,earlier.2.2⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨member,later.2.2⟩)
  have mirror : fwd.card = bwd.card := by
    apply Finset.card_equiv (Equiv.prodComm (Fin n) (Fin n))
    rintro ⟨u, v⟩
    simp only [fwd,bwd,all,forwardVertexPairs,mem_filter,mem_offDiag,Equiv.prodComm_apply,Prod.swap_prod_mk]
    exact ⟨fun ⟨⟨hu,hv,ne⟩,ordered⟩ => ⟨⟨hv,hu,ne.symm⟩,ordered⟩,
      fun ⟨⟨hv,hu,ne⟩,ordered⟩ => ⟨⟨hu,hv,ne.symm⟩,ordered⟩⟩
  have off := congrArg Finset.card covers
  rw [card_union_of_disjoint disjoint,← mirror] at off
  have count : all.card = path.length*path.length-path.length := by
    rw [show all = path.toFinset.offDiag from rfl,Finset.offDiag_card,List.toFinset_card_of_nodup simple]
  have order : path.length ≤ path.length*path.length := by
    cases length : path.length with
    | zero => simp
    | succ k => exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  rw [count] at off
  have total := Nat.sub_add_cancel order
  change 2*fwd.card+path.length = path.length^2
  rw [pow_two]
  omega

/-- Each ordered pair of distinct vertices appears in that order on at most
one row under half-bridge exclusion through size two. Count all comparisons
and apply Cauchy--Schwarz to the row lengths. -/
theorem listMass_square_le_halfTwo {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k) :
    let M := ∑ i, (paths i).length
    M^2 ≤ p*(2*(n*n-n)+M) := by
  let M := ∑ i, (paths i).length
  let pairs := (univ : Finset (Fin p)).sigma (fun i => forwardVertexPairs (paths i))
  let distinct := (univ : Finset (Fin n)).offDiag
  let forget (x : pairs) : distinct := ⟨x.val.2,mem_offDiag.mpr ⟨mem_univ _,mem_univ _,
    listBefore_ne (forwardVertexPairs_before (mem_sigma.mp x.property).2)⟩⟩
  have injective : Function.Injective forget := by
    intro a b equality
    have pairEq : a.val.2 = b.val.2 := congrArg Subtype.val equality
    have first := forwardVertexPairs_before (mem_sigma.mp a.property).2
    have second := forwardVertexPairs_before (mem_sigma.mp b.property).2
    rw [← pairEq] at second
    have index : a.val.1 = b.val.1 := by
      by_contra different
      exact no_parallel_list_steps free cutoff different first second
    exact Subtype.ext (Sigma.ext index (heq_of_eq pairEq))
  have comparisons : (∑ i : Fin p, (forwardVertexPairs (paths i)).card) ≤ n*n-n := by
    have inject := Fintype.card_le_of_injective forget injective
    simpa only [Fintype.card_coe,pairs,distinct,card_sigma,offDiag_card,card_univ,Fintype.card_fin] using inject
  have total : 2*(∑ i : Fin p, (forwardVertexPairs (paths i)).card)+M = ∑ i, (paths i).length^2 := by
    unfold M
    rw [mul_sum,← sum_add_distrib]
    exact sum_congr rfl (fun i _ => forwardVertexPairs_twice (paths i) (simple i))
  have squares : M^2 ≤ p*(∑ i : Fin p, (paths i).length^2) := by
    simpa [M] using
      sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset (Fin p)) (fun _ => 1) (fun i => (paths i).length)
  rw [← total] at squares
  exact squares.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ comparisons) _))

private theorem mass_le_eight_of_small_budget {n p M : ℕ} (hn : 0 < n) (hp : 0 < p) (small : min n p ≤ 29)
    (moment : M^2 ≤ p*(2*(n*n-n)+M)) : M ≤ 8*max n p := by
  have n0 : (0:ℝ) < n := by exact_mod_cast hn
  have p0 : (0:ℝ) < p := by exact_mod_cast hp
  have nSquare : n ≤ n*n := Nat.le_mul_of_pos_right _ hn
  have bound : (M:ℝ)^2 ≤ (p:ℝ)*(2*((n:ℝ)^2-(n:ℝ))+M) := by
    have cast : (↑(M^2) : ℝ) ≤ ↑(p*(2*(n*n-n)+M)) := Nat.cast_le.mpr moment
    simpa only [Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_sub nSquare,Nat.cast_ofNat,pow_two] using cast
  by_cases order : n ≤ p
  · rw [max_eq_right order]
    rw [min_eq_left order] at small
    by_contra! many
    have high : 8*(p:ℝ) < M := by exact_mod_cast many
    have gap := mul_pos (show (0:ℝ) < M by linarith) (sub_pos.mpr high)
    have orderR : (n:ℝ) ≤ p := by exact_mod_cast order
    have nCap : (n:ℝ) ≤ 29 := by exact_mod_cast small
    have part₁ := mul_nonneg (by norm_num : (0:ℝ) ≤ 7) (sub_nonneg.mpr high.le)
    have part₂ := mul_nonneg (by norm_num : (0:ℝ) ≤ 56) (sub_nonneg.mpr orderR)
    have part₃ := mul_nonneg (by positivity : 0 ≤ 2*(n:ℝ)) (sub_nonneg.mpr nCap)
    have factor := mul_nonneg p0.le (add_nonneg (add_nonneg part₁ part₂) part₃)
    nlinarith
  · have order' := le_of_not_ge order
    rw [max_eq_left order']
    rw [min_eq_right order'] at small
    by_contra! many
    have high : 8*(n:ℝ) < M := by exact_mod_cast many
    have gap := mul_pos (show (0:ℝ) < M by linarith) (sub_pos.mpr high)
    have orderR : (p:ℝ) ≤ n := by exact_mod_cast order'
    have pCap : (p:ℝ) ≤ 29 := by exact_mod_cast small
    have extra := mul_nonneg (sub_nonneg.mpr high.le) (show 0 ≤ 8*(n:ℝ)-(p:ℝ) by linarith)
    have quadratic := mul_nonneg (show 0 ≤ 58-2*(p:ℝ) by linarith) (sq_nonneg (n:ℝ))
    have linear := mul_nonneg (show 0 ≤ 6*(n:ℝ) by positivity) (sub_nonneg.mpr orderR)
    nlinarith

/-- At a positive budget at most 29 on either side, the exact ordered-pair
count ensures that the existing low-mass witness applies. -/
theorem regularization_list_frozen_small_budget {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : min n p ≤ 29) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_low_mass paths simple free cutoff hn hp dense long
    (mass_le_eight_of_small_budget hn hp small (listMass_square_le_halfTwo paths simple free cutoff))

/-- At either unrestricted maximum with one positive budget at most 29,
a witness meets all four frozen caps and retains at least one eighth of
the mass. It excludes full bridges through the input cutoff. -/
theorem localOrderExtremal_frozen_up_to_twenty_nine (n p k : ℕ) (half : Bool) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (small : min n p ≤ 29) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
        M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths, simple, allowed, maximal, dense, long⟩ := localOrderExtremal_isDense n p k half hn hp
  have free : HalfBridgeFree (ListBefore paths) k := by
    cases half
    · exact allowed.halfFree
    · exact allowed
  exact ⟨paths, simple, allowed, maximal,
    regularization_list_frozen_small_budget paths simple free cutoff hn hp dense long small⟩

end OnlineReachabilityPreservers
