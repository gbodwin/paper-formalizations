import MinorFreeSpanners.SmallStarRestriction

/-! Internally choose the literal low-degree centers and retain their full
mate-free stars. The degree scale may exceed the regular left degree. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- A real degree threshold gives a genuine retained-center count. This
constructs both the finite center subset and its restricted star assignment. -/
theorem exists_regular_small_star_centers (G : SimpleGraph V) (A B : Finset V)
    (ell m : ℕ) (K d q : ℝ) (L : V → Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hK : 1 ≤ K) (hd : 0 < d)
    (hmd : (m:ℝ) ≤ d) (hreg : ∀ a ∈ A, G.degree a=m)
    (hsize : A.card=ell*B.card)
    (hL : IsStarPacking G A B ell L) (hfull : ∀ b ∈ B, (L b).card=ell)
    (hfree : ∀ b ∈ B, MateFreeOn G q (insert b (L b:Set V))) :
    ∃ C : Finset V, ∃ M : V → Finset V,
      C ⊆ B ∧ IsStarPacking G A C ell M ∧
      (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b:Set V))) ∧
      (∀ x ∈ C ∪ C.biUnion M, (G.degree x:ℝ) ≤ K*d) ∧
      K*(C.card:ℝ)+ell*B.card ≥ K*B.card := by
  classical
  let C := B.filter fun b => (G.degree b:ℝ) ≤ K*d
  let R := B.filter fun b => K*d < (G.degree b:ℝ)
  let M := fun b => if b ∈ C then L b else ∅
  have hCB : C ⊆ B := Finset.filter_subset _ _
  have hM : IsStarPacking G A C ell M := hL.restrict_centers
  have hpartition : C.card+R.card=B.card := by
    simpa only [C,R,not_le] using Finset.card_filter_add_card_filter_not
      (s:=B) (fun b => (G.degree b:ℝ) ≤ K*d)
  have hsum : ∑ b ∈ B, G.degree b=m*A.card := by
    rw [isBipartiteWith_sum_degrees_eq_card_edges' hG,
      ← isBipartiteWith_sum_degrees_eq_card_edges hG]
    calc
      _ = ∑ _a ∈ A, m := Finset.sum_congr rfl hreg
      _ = _ := by simp [Nat.mul_comm]
  have hsumR : ∑ b ∈ B, (G.degree b:ℝ)=(m:ℝ)*A.card := by exact_mod_cast hsum
  have hremoved : K*d*(R.card:ℝ) ≤ d*((ell:ℝ)*B.card) := calc
    _ = ∑ _b ∈ R, K*d := by simp [mul_comm]
    _ ≤ ∑ b ∈ R, (G.degree b:ℝ) := Finset.sum_le_sum
      (fun b hb => (Finset.mem_filter.mp hb).2.le)
    _ ≤ ∑ b ∈ B, (G.degree b:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = (m:ℝ)*A.card := hsumR
    _ ≤ d*A.card := mul_le_mul_of_nonneg_right hmd (Nat.cast_nonneg _)
    _ = _ := by rw [hsize]; push_cast; ring
  have hremoved' : K*(R.card:ℝ) ≤ ell*B.card := by nlinarith
  refine ⟨C,M,hCB,hM,?_,?_,?_,?_⟩
  · intro b hb
    simpa [M,hb] using hfull b (hCB hb)
  · intro b hb
    simpa [M,hb] using hfree b (hCB hb)
  · intro x hx
    rcases Finset.mem_union.mp hx with hc|hl
    · exact (Finset.mem_filter.mp hc).2
    · obtain ⟨b,_,hx⟩ := Finset.mem_biUnion.mp hl
      rw [hreg x (hM.2.1 b hx)]
      nlinarith
  · have hp : (C.card:ℝ)+R.card=B.card := by exact_mod_cast hpartition
    nlinarith

end MinorFreeSpanners
