import LinearDistancePreservers.DirectionGraph
import Mathlib.Tactic

/-! Convex integer chains, the geometric part of the planar sharp
direction construction. Positive horizontal increments with strictly
increasing slopes give one exposed vertex per cut. Counting enough
primitive slopes remains a separate obligation. -/
namespace LinearDistancePreservers.ConvexChains
open Finset
attribute [local instance] Classical.propDecidable

def partialSum {m : ℕ} (a : Fin m → ℕ) (t : Fin (m+1)) : ℕ :=
  ∑ i : Fin m, if i.val < t.val then a i else 0

def vector {m : ℕ} (a b : Fin m → ℕ) (t : Fin (m+1)) : Bool → ℕ :=
  fun q => if q then partialSum b t else partialSum a t

noncomputable def score {m : ℕ} (a b : Fin m → ℕ) (θ : ℝ)
    (t : Fin (m+1)) : ℝ :=
  θ*(partialSum a t : ℝ)-(partialSum b t : ℝ)

theorem score_eq_sum {m : ℕ} (a b : Fin m → ℕ) (θ : ℝ)
    (t : Fin (m+1)) :
    score a b θ t =
      ∑ i : Fin m, if i.val < t.val then θ*(a i : ℝ)-(b i : ℝ) else 0 := by
  unfold score partialSum
  rw [Nat.cast_sum, Nat.cast_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Separate the slopes before and after any cut, including both ends. -/
theorem separating_cut {m : ℕ} (r : Fin m → ℝ) (hr : StrictMono r)
    (t : Fin (m+1)) :
    ∃ θ : ℝ, (∀ i : Fin m, i.val < t.val → r i < θ) ∧
      (∀ i : Fin m, t.val ≤ i.val → θ < r i) := by
  have ht : t.val ≤ m := by omega
  by_cases hm : m = 0
  · subst m
    exact ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  have hmpos : 0 < m := by omega
  by_cases hzero : t.val = 0
  · let first : Fin m := ⟨0, hmpos⟩
    refine ⟨r first-1, ?_, ?_⟩
    · intro i hi
      omega
    · intro i _
      have hle : r first ≤ r i := hr.monotone (by change 0 ≤ i.val; omega)
      linarith
  by_cases hlast : t.val = m
  · let last : Fin m := ⟨m-1, by omega⟩
    refine ⟨r last+1, ?_, ?_⟩
    · intro i _
      have hle : r i ≤ r last := hr.monotone (by change i.val ≤ m-1; omega)
      linarith
    · intro i hi
      omega
  let left : Fin m := ⟨t.val-1, by omega⟩
  let right : Fin m := ⟨t.val, by omega⟩
  have hlt : r left < r right := hr (by change t.val-1 < t.val; omega)
  obtain ⟨θ, hleft, hright⟩ := exists_between hlt
  refine ⟨θ, ?_, ?_⟩
  · intro i hi
    exact lt_of_le_of_lt (hr.monotone (by change i.val ≤ t.val-1; omega)) hleft
  · intro i hi
    exact lt_of_lt_of_le hright (hr.monotone (by change t.val ≤ i.val; exact hi))

/-- Each cut is the unique maximum of a concrete linear functional. -/
theorem exposed {m : ℕ} (a b : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (hs : StrictMono (fun i => (b i : ℝ)/(a i : ℝ))) (t : Fin (m+1)) :
    ∃ θ : ℝ, ∀ j : Fin (m+1), j ≠ t → score a b θ j < score a b θ t := by
  obtain ⟨θ,hbefore,hafter⟩ := separating_cut _ hs t
  have hpos (i : Fin m) (hi : i.val < t.val) :
      0 < θ*(a i : ℝ)-(b i : ℝ) := by
    have hai : (0 : ℝ) < a i := by exact_mod_cast ha i
    have hh := (div_lt_iff₀ hai).mp (hbefore i hi)
    nlinarith
  have hneg (i : Fin m) (hi : t.val ≤ i.val) :
      θ*(a i : ℝ)-(b i : ℝ) < 0 := by
    have hai : (0 : ℝ) < a i := by exact_mod_cast ha i
    have hh := (lt_div_iff₀ hai).mp (hafter i hi)
    nlinarith
  refine ⟨θ, ?_⟩
  intro j hne
  rw [score_eq_sum, score_eq_sum]
  apply sum_lt_sum
  · intro i _
    by_cases hit : i.val < t.val
    · have hh := hpos i hit
      by_cases hij : i.val < j.val
      · simp [hit,hij]
      · simp only [if_pos hit,if_neg hij]
        exact hh.le
    · have hh := hneg i (by omega)
      by_cases hij : i.val < j.val
      · simp only [if_neg hit,if_pos hij]
        exact hh.le
      · simp [hit,hij]
  · have ht : t.val ≤ m := by omega
    rcases lt_or_gt_of_ne hne with hjt | htj
    · let i : Fin m := ⟨j.val, by change j.val < t.val at hjt; omega⟩
      refine ⟨i, mem_univ i, ?_⟩
      have hbefore' : i.val < t.val := hjt
      have hnot : ¬ i.val < j.val := by simp [i]
      simpa only [if_neg hnot,if_pos hbefore'] using hpos i hbefore'
    · let i : Fin m := ⟨t.val, by change t.val < j.val at htj; omega⟩
      refine ⟨i, mem_univ i, ?_⟩
      have hbefore' : i.val < j.val := htj
      have hnot : ¬ i.val < t.val := by simp [i]
      simpa only [if_pos hbefore',if_neg hnot] using hneg i (by simp [i])

theorem vector_injective {m : ℕ} (a b : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (hs : StrictMono (fun i => (b i : ℝ)/(a i : ℝ))) :
    Function.Injective (vector a b) := by
  intro j t h
  by_contra hne
  obtain ⟨θ,hθ⟩ := exposed a b ha hs t
  have hx := congrFun h false
  have hy := congrFun h true
  simp [vector] at hx hy
  have heq : score a b θ j = score a b θ t := by rw [score,score,hx,hy]
  exact (ne_of_lt (hθ j hne)) heq

/-- Actual bounded integer vectors with no nonconstant average at a vertex. -/
theorem average_rigid {m : ℕ} (a b : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (hs : StrictMono (fun i => (b i : ℝ)/(a i : ℝ))) :
    DirectionGraph.AverageRigid (vector a b) := by
  intro n t f hsum i
  by_cases hi : f i = t
  · rw [hi]
  obtain ⟨θ,hθ⟩ := exposed a b ha hs t
  have hle (j : Fin n) : score a b θ (f j) ≤ score a b θ t := by
    by_cases hj : f j = t
    · rw [hj]
    · exact (hθ (f j) hj).le
  have hlt : ∑ j : Fin n, score a b θ (f j) <
      ∑ j : Fin n, score a b θ t :=
    sum_lt_sum (fun j _ => hle j) ⟨i,mem_univ i,hθ (f i) hi⟩
  have hx : ∑ j : Fin n, (partialSum a (f j) : ℝ) = (n : ℝ)*(partialSum a t : ℝ) := by
    have hh := hsum false
    simp [vector] at hh
    exact_mod_cast hh
  have hy : ∑ j : Fin n, (partialSum b (f j) : ℝ) = (n : ℝ)*(partialSum b t : ℝ) := by
    have hh := hsum true
    simp [vector] at hh
    exact_mod_cast hh
  have heq : ∑ j : Fin n, score a b θ (f j) = (n : ℝ)*score a b θ t := by
    simp only [score,sum_sub_distrib,← mul_sum,hx,hy]
    ring
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hlt
  linarith

theorem prefix_le {m R : ℕ} (a : Fin m → ℕ) (ha : ∀ i, a i ≤ R)
    (t : Fin (m+1)) : partialSum a t ≤ m*R := by
  unfold partialSum
  calc
    _ ≤ ∑ _i : Fin m, R := sum_le_sum (by
      intro i _
      split_ifs
      · exact ha i
      · exact Nat.zero_le _)
    _ = m*R := by simp

/-- From m ordered lattice slopes bounded by R, construct m+1 distinct
average-rigid directions in a square of side mR+1. No graph premise. -/
theorem exists_directions {m R : ℕ} (a b : Fin m → ℕ)
    (ha : ∀ i, 0 < a i) (haR : ∀ i, a i ≤ R) (hbR : ∀ i, b i ≤ R)
    (hs : StrictMono (fun i => (b i : ℝ)/(a i : ℝ))) :
    ∃ v : Fin (m+1) → Bool → ℕ,
      Function.Injective v ∧ (∀ t q, v t q < m*R+1) ∧
        DirectionGraph.AverageRigid v := by
  refine ⟨vector a b,vector_injective a b ha hs,?_,average_rigid a b ha hs⟩
  intro t q
  cases q
  · exact Nat.lt_succ_of_le (prefix_le a haR t)
  · exact Nat.lt_succ_of_le (prefix_le b hbR t)


/-- An explicit growing planar family, with only a positive integer as
input. This quadratic-box family is weaker than the sharp 2/3 exponent. -/
theorem staircase_directions {R : ℕ} (hR : 0 < R) :
    ∃ v : Fin (R+1) → Bool → ℕ,
      Function.Injective v ∧ (∀ t q, v t q < R^2+1) ∧
        DirectionGraph.AverageRigid v := by
  let a : Fin R → ℕ := fun _ => 1
  let b : Fin R → ℕ := fun i => i.val+1
  have hs : StrictMono (fun i => (b i : ℝ)/(a i : ℝ)) := by
    intro i j hij
    simp only [a,b,Nat.cast_one,div_one]
    exact_mod_cast Nat.succ_lt_succ (show i.val < j.val from hij)
  simpa only [pow_two] using exists_directions a b (by intro i; simp [a])
    (by intro i; exact hR) (by intro i; dsimp [b]; omega) hs

end LinearDistancePreservers.ConvexChains
