import LinearDistancePreservers.Branching
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! The batching step in Theorem 1, including the integer cube-root choice.
This is a bound on a `Routing` already supplied with the consistency data.
It does not assert that a consistent shortest-path selection has been built. -/
namespace LinearDistancePreservers.Routing
open Finset
variable {I J V : Type*}

def restrict (R : Routing I V) (S : Type*) (f : S → I) : Routing S V where
  pred i := R.pred (f i)
  rank i := R.rank (f i)
  rank_inj i := R.rank_inj (f i)
  consistent i j := R.consistent (f i) (f j)

variable [Fintype I] [Fintype J] [Fintype V] [DecidableEq V]

theorem partition_bound (R : Routing I V) (bucket : I → J) (q : ℕ)
    [DecidableEq J]
    (hsize : ∀ j, Fintype.card {i : I // bucket i = j} ≤ q) :
    R.edges.card ≤ Fintype.card J * (2 * Fintype.card V + q^3) := by
  classical
  let part (j : J) := R.restrict {i : I // bucket i = j} Subtype.val
  have hcover : R.edges ⊆ univ.biUnion (fun j => (part j).edges) := by
    intro e he
    obtain ⟨i,hi⟩ := R.mem_tails.mp (mem_filter.mp he).2
    apply mem_biUnion.mpr
    refine ⟨bucket i,mem_univ _,?_⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    apply ((part (bucket i)).mem_tails).mpr
    exact ⟨⟨i,rfl⟩,hi⟩
  calc
    R.edges.card ≤ (univ.biUnion (fun j => (part j).edges)).card := card_le_card hcover
    _ ≤ ∑ j : J, (part j).edges.card := card_biUnion_le
    _ ≤ ∑ _j : J, (2 * Fintype.card V + q^3) := sum_le_sum fun j _ =>
      ((part j).edges_card_le).trans (Nat.add_le_add_left (Nat.pow_le_pow_left (hsize j) 3) _)
    _ = _ := by simp

/-- Partition p routes into floor(p/q)+1 blocks of size at most q. -/
theorem batch_bound {p q : ℕ} (hq : 0 < q) (R : Routing (Fin p) V) :
    R.edges.card ≤ (p/q+1) * (2 * Fintype.card V + q^3) := by
  classical
  let bucket : Fin p → Fin (p/q+1) := fun i =>
    ⟨i.val/q, Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le)⟩
  have hsize (j : Fin (p/q+1)) : Fintype.card {i : Fin p // bucket i = j} ≤ q := by
    let f : {i : Fin p // bucket i = j} → Fin q := fun i =>
      ⟨i.val.val % q, Nat.mod_lt _ hq⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Fin.ext
      have hmod : a.val.val % q = b.val.val % q := congrArg Fin.val hab
      have hdiv : a.val.val / q = b.val.val / q := by
        have := congrArg Fin.val (a.property.trans b.property.symm)
        exact this
      have ha := Nat.mod_add_div a.val.val q
      have hb := Nat.mod_add_div b.val.val q
      rw [hdiv,hmod] at ha
      omega
    simpa using Fintype.card_le_of_injective f hf
  simpa using R.partition_bound bucket q hsize

/-- The finite integer form of the asymptotic O(n+n^(2/3)p) estimate. -/
theorem cube_root_bound {p q : ℕ} (R : Routing (Fin p) V)
    (hq : 0 < q) (hlow : q^3 ≤ Fintype.card V)
    (hhigh : Fintype.card V < (q+1)^3) :
    R.edges.card ≤ 3 * Fintype.card V + 24 * p * q^2 := by
  have hb := R.batch_bound hq
  have hn : Fintype.card V ≤ 8*q^3 := by
    have hq' : q+1 ≤ 2*q := by omega
    have := Nat.pow_le_pow_left hq' 3
    norm_num [mul_pow] at this
    omega
  have hd : (p/q)*q ≤ p := Nat.div_mul_le_self p q
  have hdn : (p/q)*Fintype.card V ≤ (p/q)*(8*q^3) := Nat.mul_le_mul_left _ hn
  have hdq : (p/q)*q*q^2 ≤ p*q^2 := Nat.mul_le_mul_right _ hd
  calc
    R.edges.card ≤ (p/q+1)*(2*Fintype.card V+q^3) := hb
    _ ≤ (p/q+1)*(3*Fintype.card V) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 3*Fintype.card V+24*p*q^2 := by nlinarith

/-- The cube-root parameter exists canonically for every nonempty vertex set. -/
theorem integer_theorem_one {p : ℕ} (R : Routing (Fin p) V)
    (hn : 0 < Fintype.card V) :
    R.edges.card ≤ 3 * Fintype.card V +
      24 * p * (Nat.nthRoot 3 (Fintype.card V))^2 := by
  let q := Nat.nthRoot 3 (Fintype.card V)
  have hlow : q^3 ≤ Fintype.card V := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hhigh : Fintype.card V < (q+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hq : 0 < q := by
    by_contra h
    have hz : q = 0 := by omega
    rw [hz] at hhigh
    norm_num at hhigh
    omega
  exact R.cube_root_bound hq hlow hhigh

end LinearDistancePreservers.Routing
