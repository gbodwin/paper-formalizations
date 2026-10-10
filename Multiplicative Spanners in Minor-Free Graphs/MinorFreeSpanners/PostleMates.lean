import MinorFreeSpanners.PostleBudget
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The actual induced-subgraph argument of Postle, arXiv:2006.14945v3,
Proposition 3.2. The selected vertex is omitted from the induced vertex set:
all required common-neighbor incidences remain, and the stated 3Kd bound then
holds throughout K,d>=1. This closes the harmless displayed rounding gap. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A genuine induced subgraph containing every selected mate and every
neighbor of v has at least half the selected common-neighbor incidence count. -/
theorem common_neighbor_induced_count (G : SimpleGraph V) (v : V) (M : Finset V) :
    ∃ S : Finset V, S.card ≤ G.degree v + M.card ∧
      (∑ w : M, Fintype.card (G.commonNeighbors v w.val)) ≤
        2*(G.induce (S:Set V)).edgeFinset.card := by
  classical
  let S := G.neighborFinset v ∪ M
  let H := G.induce (S:Set V)
  let f : M → S := fun w => ⟨w.val,Finset.mem_union.mpr (Or.inr w.property)⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg (fun x : S => x.val) h)
  have hdeg : ∀ w : M, Fintype.card (G.commonNeighbors v w.val) ≤ H.degree (f w) := by
    intro w
    let g : G.commonNeighbors v w.val → H.neighborSet (f w) := fun x =>
      ⟨⟨x.val,Finset.mem_union.mpr (Or.inl ((G.mem_neighborFinset v x.val).mpr x.property.1))⟩,
        x.property.2⟩
    have hg : Function.Injective g := by
      intro a b h
      exact Subtype.ext (congrArg (fun x => x.val.val) h)
    rw [← H.card_neighborSet_eq_degree]
    exact Fintype.card_le_of_injective g hg
  refine ⟨S,?_,?_⟩
  · exact (Finset.card_union_le _ _).trans_eq (by rw [G.card_neighborFinset_eq_degree])
  · calc
      _ ≤ ∑ x : S, H.degree x := Finset.sum_le_sum_of_injOn f
        (fun a _ b _ h => hf h) (Finset.subset_univ _)
        (fun w _ => hdeg w) (fun _ _ _ => Nat.zero_le _)
      _ = _ := H.sum_degrees_eq_twice_card_edges

/-- An actual small vertex and many actual common-neighbor mates produce
an actual small dense induced subgraph, throughout the printed real domain. -/
theorem postle_mated_vertex (G : SimpleGraph V) (v : V)
    (K d ε₁ ε₂ : ℝ) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂0 : 0 ≤ ε₂)
    (hsmall : (G.degree v:ℝ) ≤ K*d)
    (hmates : ε₁*d ≤ ((Finset.univ.filter fun w =>
      ε₂*d ≤ (Fintype.card (G.commonNeighbors v w):ℝ)).card:ℝ)) :
    ∃ S : Finset V, (S.card:ℝ) ≤ 3*K*d ∧
      ε₁*ε₂*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ) := by
  classical
  let mates := Finset.univ.filter fun w =>
    ε₂*d ≤ (Fintype.card (G.commonNeighbors v w):ℝ)
  have hceil : ⌈ε₁*d⌉₊ ≤ mates.card := Nat.ceil_le.mpr hmates
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hceil
  obtain ⟨S,hS,hE⟩ := common_neighbor_induced_count G v M
  have hd0 : 0 ≤ d := by linarith
  have hKd : d ≤ K*d := by nlinarith
  have hround := Nat.ceil_lt_add_one (mul_nonneg hε₁0 hd0)
  have hproduct : ε₁*d ≤ d := by nlinarith
  have hmcard : (M.card:ℝ) = (⌈ε₁*d⌉₊:ℝ) := by exact_mod_cast hcard
  have hinc : (M.card:ℝ)*(ε₂*d) ≤
      (∑ w : M, Fintype.card (G.commonNeighbors v w.val):ℕ) := by
    have hh : ∀ w : M, ε₂*d ≤ (Fintype.card (G.commonNeighbors v w.val):ℝ) := by
      intro w
      exact (Finset.mem_filter.mp (hM w.property)).2
    calc
      _ = ∑ w : M, (ε₂*d) := by simp
      _ ≤ ∑ w : M, (Fintype.card (G.commonNeighbors v w.val):ℝ) :=
        Finset.sum_le_sum (fun w _ => hh w)
      _ = _ := by norm_cast
  have hrealE : (∑ w : M, Fintype.card (G.commonNeighbors v w.val):ℕ) ≤
      (2:ℝ)*((G.induce (S:Set V)).edgeFinset.card:ℝ) := by exact_mod_cast hE
  have hlower : ε₁*d ≤ (M.card:ℝ) := by
    rw [hmcard]
    exact Nat.le_ceil _
  refine ⟨S,?_,?_⟩
  · have hsreal : (S.card:ℝ) ≤ (G.degree v:ℝ)+(M.card:ℝ) := by exact_mod_cast hS
    rw [hmcard] at hsreal
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_right hlower (mul_nonneg hε₂0 hd0)
    nlinarith

/-- Postle's literal small-vertex unmatedness condition, measured using
actual graph common neighbors and distinct host vertices. -/
def Unmated (G : SimpleGraph V) (K ε₁ ε₂ d : ℝ) : Prop :=
  ∀ v, (G.degree v:ℝ) ≤ K*d →
    ((Finset.univ.filter fun w =>
      ε₂*d ≤ (Fintype.card (G.commonNeighbors v w):ℝ)).card:ℝ) < ε₁*d

/-- Proposition 3.2, with the original constant 3 and its complete real
parameter domain. The dense alternative is an actual induced subgraph.
The proof uses N(v) union the selected mates, omitting the unnecessary v. -/
theorem postle_small_dense_or_unmated (G : SimpleGraph V)
    (K d ε₁ ε₂ : ℝ) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hε₂0 : 0 ≤ ε₂) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*K*d ∧
      ε₁*ε₂*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
      Unmated G K ε₁ ε₂ d := by
  classical
  by_cases h : Unmated G K ε₁ ε₂ d
  · exact Or.inr h
  · unfold Unmated at h
    push_neg at h
    obtain ⟨v,hsmall,hmates⟩ := h
    exact Or.inl (postle_mated_vertex G v K d ε₁ ε₂ hK hd hε₁0 hε₁1 hε₂0 hsmall hmates)

end MinorFreeSpanners
