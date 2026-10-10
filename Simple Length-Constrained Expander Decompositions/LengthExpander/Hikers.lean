import LengthExpander.ParallelGreedy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A reusable hiker protocol for ordered matching permutations. The process
constructs actual graph walks and proves its exact total-traversal invariant. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LengthExpander
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Positions remain a permutation, so there is one hiker at each vertex. -/
def hikerPosition (σ : ℕ → Equiv.Perm V) : ℕ → Equiv.Perm V
  | 0 => Equiv.refl V
  | k+1 => (hikerPosition σ k).trans (σ k)

noncomputable def moved (σ : Equiv.Perm V) (v : V) : ℕ := by
  classical
  exact if σ v = v then 0 else 1

noncomputable def hikerTravel (σ : ℕ → Equiv.Perm V) : ℕ → V → ℕ
  | 0, _ => 0
  | k+1, v => hikerTravel σ k v + moved (σ k) (hikerPosition σ k v)

noncomputable def hikerWalk (σ : ℕ → Equiv.Perm V)
    (hedge : ∀ k v, σ k v ≠ v → G.Adj v (σ k v)) :
    (k : ℕ) → (v : V) → G.Walk v (hikerPosition σ k v)
  | 0, v => .nil
  | k+1, v => by
    classical
    by_cases he : σ k (hikerPosition σ k v) = hikerPosition σ k v
    · exact (hikerWalk σ hedge k v).copy rfl he.symm
    · exact (hikerWalk σ hedge k v).concat (hedge k _ he)

theorem hikerWalk_length (σ : ℕ → Equiv.Perm V)
    (hedge : ∀ k v, σ k v ≠ v → G.Adj v (σ k v)) (k : ℕ) (v : V) :
    (hikerWalk σ hedge k v).length = hikerTravel σ k v := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases he : σ k (hikerPosition σ k v) = hikerPosition σ k v
    · simp [hikerWalk, he, hikerTravel, moved, Walk.length_copy, Walk.length_concat, ih]
    · simp [hikerWalk, he, hikerTravel, moved, Walk.length_copy, Walk.length_concat, ih]

theorem hikerWalk_increasing (σ : ℕ → Equiv.Perm V)
    (hedge : ∀ k v, σ k v ≠ v → G.Adj v (σ k v)) (index : Sym2 V → ℕ)
    (hindex : ∀ k v, σ k v ≠ v → index s(v,σ k v) = k) (k : ℕ) (v : V) :
    Increasing index (hikerWalk σ hedge k v) ∧
      (∀ e ∈ (hikerWalk σ hedge k v).edges, index e < k) := by
  classical
  induction k with
  | zero => simp [hikerWalk, Increasing, Walk.edges_nil]
  | succ k ih =>
    by_cases he : σ k (hikerPosition σ k v) = hikerPosition σ k v
    · constructor
      · simpa [hikerWalk, he, Increasing, Walk.edges_copy] using ih.1
      · intro e he'
        simp only [hikerWalk, dif_pos he, Walk.edges_copy] at he'
        exact lt_trans (ih.2 e he') (Nat.lt_succ_self _)
    · have hi := hindex k (hikerPosition σ k v) he
      constructor
      · simp only [hikerWalk, dif_neg he]
        apply (increasing_concat_iff _ _).2
        exact ⟨ih.1, fun e he' => by change index e < index s(hikerPosition σ k v,σ k (hikerPosition σ k v)); rw [hi]; exact ih.2 e he'⟩
      · intro e he'
        simp only [hikerWalk, dif_neg he, Walk.edges_concat, List.concat_eq_append,
          List.mem_append, List.mem_singleton] at he'
        rcases he' with he' | rfl
        · exact lt_trans (ih.2 e he') (Nat.lt_succ_self _)
        · change index s(hikerPosition σ k v, σ k (hikerPosition σ k v)) < k + 1
          rw [hi]; exact Nat.lt_succ_self _

variable [Fintype V]

noncomputable def movedCount (σ : Equiv.Perm V) : ℕ := ∑ v, moved σ v

/-- Every traversal is counted once; a matching contributes two per edge.
The equality itself works for arbitrary permutations. -/
theorem hiker_total_travel (σ : ℕ → Equiv.Perm V) (k : ℕ) :
    (∑ v, hikerTravel σ k v) = ∑ i ∈ range k, movedCount (σ i) := by
  induction k with
  | zero => simp [hikerTravel]
  | succ k ih =>
    simp only [hikerTravel, sum_add_distrib, sum_range_succ, ih]
    congr 1
    exact Equiv.sum_comp (hikerPosition σ k) (moved (σ k))

/-- The averaging step in the weak counting argument. -/
theorem exists_hiker_long [Nonempty V] (σ : ℕ → Equiv.Perm V) (k r : ℕ)
    (hcount : Fintype.card V * r ≤ ∑ i ∈ range k, movedCount (σ i)) :
    ∃ v, r ≤ hikerTravel σ k v := by
  classical
  by_contra hn
  have hlt : ∀ v : V, hikerTravel σ k v < r := by
    intro v
    exact lt_of_not_ge (fun hv => hn ⟨v,hv⟩)
  have hsum : (∑ v, hikerTravel σ k v) < ∑ _v : V, r :=
    sum_lt_sum_of_nonempty univ_nonempty (fun v _ => hlt v)
  rw [hiker_total_travel] at hsum
  simp only [sum_const, card_univ, smul_eq_mul] at hsum
  omega

end LengthExpander
