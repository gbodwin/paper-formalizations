import MinorFreeSpanners.MateFreeStarContraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Remove actual large centers from a full star cover. The retained stars
are small at every vertex and lose only the degree-counted number of vertices;
this precedes and does not assume the later bad-pair cleaning argument. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Literal degree counting bounds the number of large right-side centers. -/
theorem large_centers_card_bound (G : SimpleGraph V) (A B : Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (ell d : ℕ) (K : ℝ)
    (hd : 0 < d) (hreg : ∀ x ∈ A, G.degree x = d)
    (hsize : A.card = ell*B.card) :
    K*((B.filter fun b => K*d < (G.degree b:ℝ)).card:ℝ) ≤ ell*B.card := by
  classical
  let D := B.filter fun b => K*d < (G.degree b:ℝ)
  have hsum : ∑ b ∈ B, G.degree b = d*A.card := by
    rw [isBipartiteWith_sum_degrees_eq_card_edges' hG,
      ← isBipartiteWith_sum_degrees_eq_card_edges hG]
    calc
      _ = ∑ a ∈ A, d := Finset.sum_congr rfl hreg
      _ = _ := by simp [Nat.mul_comm]
  have hsumR : ∑ b ∈ B, (G.degree b:ℝ) = d*A.card := by exact_mod_cast hsum
  have hb : K*d*(D.card:ℝ) ≤ d*A.card := calc
    _ = ∑ _b ∈ D, (K*d) := by simp [mul_comm]
    _ ≤ ∑ b ∈ D, (G.degree b:ℝ) := Finset.sum_le_sum
      (fun b hb => (Finset.mem_filter.mp hb).2.le)
    _ ≤ ∑ b ∈ B, (G.degree b:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := hsumR
  rw [hsize] at hb
  push_cast at hb
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  change K*(D.card:ℝ) ≤ _
  nlinarith

/-- A full mate-free star cover contains a large actual subfamily whose every
vertex is small. This is the first deletion step of Postle Lemma4.3 only. -/
theorem exists_small_star_restriction (G : SimpleGraph V) (A B : Finset V)
    (ell d : ℕ) (K q : ℝ) (L : V → Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hd : 0 < d) (hK : 1 ≤ K)
    (hreg : ∀ x ∈ A, G.degree x = d) (hsize : A.card = ell*B.card)
    (hL : IsStarPacking G A B ell L) (hfull : ∀ b ∈ B, (L b).card = ell)
    (hcover : B.biUnion (fun b => insert b (L b)) = Finset.univ)
    (hfree : ∀ b ∈ B, MateFreeOn G q (insert b (L b:Set V))) :
    ∃ C : Finset V, ∃ M : V → Finset V,
      C ⊆ B ∧ IsStarPacking G A C ell M ∧
      (∀ b ∈ C, (M b).card = ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b:Set V))) ∧
      (∀ x ∈ C.biUnion (fun b => insert b (M b)), (G.degree x:ℝ) ≤ K*d) ∧
      K*((C.biUnion (fun b => insert b (M b))).card:ℝ) +
        ell*Fintype.card V ≥ K*Fintype.card V := by
  classical
  let C := B.filter fun b => (G.degree b:ℝ) ≤ K*d
  let M := fun b => if b ∈ C then L b else ∅
  have hCB : C ⊆ B := Finset.filter_subset _ _
  have hM : IsStarPacking G A C ell M := hL.restrict_centers
  have hf : ∀ b ∈ C, (M b).card = ell := by
    intro b hb
    simpa [M,hb] using hfull b (hCB hb)
  have hAB : Disjoint A B := Finset.disjoint_coe.mp hG.disjoint
  have hn := hL.full_branch_union_card hAB hfull
  rw [hcover,Finset.card_univ] at hn
  have hc := hM.full_branch_union_card (hAB.mono_right hCB) hf
  have hp := Finset.card_filter_add_card_filter_not (s := B)
    (fun b => (G.degree b:ℝ) ≤ K*d)
  have hp' : C.card + (B.filter fun b => K*d < (G.degree b:ℝ)).card = B.card := by
    simpa only [not_le] using hp
  have hb := large_centers_card_bound G A B hG ell d K hd hreg hsize
  have hcardR : K*(C.card:ℝ) + ell*B.card ≥ K*B.card := by
    have hpR : (C.card:ℝ) + ((B.filter fun b => K*d < (G.degree b:ℝ)).card:ℝ) = B.card := by
      exact_mod_cast hp'
    nlinarith
  refine ⟨C,M,hCB,hM,hf,?_,?_,?_⟩
  · intro b hb
    simpa [M,hb] using hfree b (hCB hb)
  · intro x hx
    obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact (Finset.mem_filter.mp hb).2
    · have hxA := hM.2.1 b hx
      rw [hreg x hxA]
      have hdR : (0:ℝ) ≤ d := Nat.cast_nonneg _
      nlinarith
  · rw [hc,hn]
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ) ≤ ell+1 by positivity)
      (show 0 ≤ K*(C.card:ℝ)+ell*B.card-K*B.card by linarith)]

end MinorFreeSpanners
