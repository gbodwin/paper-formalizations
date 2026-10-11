import MinorFreeSpanners.BoundedMinor
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Bound a genuine quotient degree by the sum of original host degrees
in its branch, using disjoint neighboring branches and actual edge witnesses. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I V : Type*} [Fintype I] [Fintype V]
variable {F : SimpleGraph I} {G : SimpleGraph V}

theorem degree_le_branch_sum (M : MinorModel F G) (i : I) :
    F.degree i ≤ ∑ x ∈ (M.branch i).toFinset, G.degree x := by
  classical
  choose a ha b hb hab using (fun j : F.neighborSet i => M.adjacent i j.val j.property)
  let S := (M.branch i).toFinset.biUnion (fun x => G.neighborFinset x)
  let f : F.neighborSet i → S := fun j =>
    ⟨b j,Finset.mem_biUnion.mpr ⟨a j,Set.mem_toFinset.mpr (ha j),by simpa using hab j⟩⟩
  have hf : Function.Injective f := by
    intro j k he
    have he' : b j=b k := congrArg Subtype.val he
    apply Subtype.ext
    exact M.branch_unique (hb j) (he' ▸ hb k)
  have hcard := Fintype.card_le_of_injective f hf
  have hcount : F.degree i ≤ S.card := by
    rw [← F.card_neighborSet_eq_degree]
    simpa only [Fintype.card_coe] using hcard
  apply hcount.trans
  calc
    S.card ≤ ∑ x ∈ (M.branch i).toFinset, (G.neighborFinset x).card :=
      Finset.card_biUnion_le
    _ = _ := by simp only [card_neighborFinset_eq_degree]

/-- A branch of at most k actual small vertices is small at the multiplied
threshold. The current quotient degree is not assumed. -/
theorem degree_le_of_branch_small (M : MinorModel F G) (i : I) (k : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hk : (M.branch i).toFinset.card ≤ k)
    (hsmall : ∀ x ∈ M.branch i, (G.degree x:ℝ) ≤ D) :
    (F.degree i:ℝ) ≤ k*D := by
  classical
  have hs : (F.degree i:ℝ) ≤ ∑ x ∈ (M.branch i).toFinset, (G.degree x:ℝ) := by
    have h : (F.degree i:ℝ) ≤ ((∑ x ∈ (M.branch i).toFinset, G.degree x:ℕ):ℝ) :=
      Nat.cast_le.mpr (M.degree_le_branch_sum i)
    simpa only [Nat.cast_sum] using h
  apply hs.trans
  calc
    (∑ x ∈ (M.branch i).toFinset, (G.degree x:ℝ)) ≤
        ∑ x ∈ (M.branch i).toFinset, D := Finset.sum_le_sum (fun x hx => hsmall x (Set.mem_toFinset.mp hx))
    _ = ((M.branch i).toFinset.card:ℝ)*D := by simp
    _ ≤ k*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hD

end MinorModel
end MinorFreeSpanners
