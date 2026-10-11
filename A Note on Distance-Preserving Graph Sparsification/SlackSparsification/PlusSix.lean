import SlackSparsification.Attachments
import SlackSparsification.PairConnector
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Theorem 11's graph construction relative to the cited Theorem 10.
The external subset-spanner input is an ordinary explicit hypothesis, not an
axiom or a claimed proved theorem. All purchases and routing are internal. -/
namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

/-- The cited Theorem 10, exposed as a premise with a uniform constant. -/
def SubsetTwoBound (G : SimpleGraph V) (C : ℝ) : Prop :=
  ∀ R : Finset V, ∃ T : SimpleGraph V, IsAdditiveSpanner G T (R ×ˢ R) 2 ∧
    (T.edgeFinset.card : ℝ) ≤ C * Fintype.card V * Real.sqrt R.card

/-- At least a quarter of long demands obtain additive error six, given
the exact subset-spanner theorem cited by the paper. -/
theorem exists_plus_six_long_of_subset (G H₀ : SimpleGraph V) (h₀G : H₀ ≤ G)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (d m : ℕ) (hd : 0 < d)
    (C : ℝ) (hC : 0 ≤ C) (hsubset : SubsetTwoBound G C)
    (hdegree : ∀ u v, G.Adj u v → ¬H₀.Adj u v → 3 * d ≤ H₀.degree u)
    (hlong : ∀ i ∈ P, 2 * m < (missingIndices H₀ (p i)).card) :
    ∃ (H : SimpleGraph V) (Q : Finset D), H ≤ G ∧ Q ⊆ P ∧ P.card ≤ 4 * Q.card ∧
      (H.edgeFinset.card : ℝ) ≤ H₀.edgeFinset.card + 2 * P.card * m +
        C * Fintype.card V * Real.sqrt (2 * (2 * Fintype.card V / (d * (m + 1)) + 1) : ℕ) ∧
      ∀ i ∈ Q, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 6 := by
  classical
  choose F N₁ N₂ hFG hFsize hN₁ hN₂ hatt using fun i : P =>
    exists_path_attachments G H₀ h₀G d m hdegree (p i.val) (hp i.val) (hlong i.val i.property)
  obtain ⟨R, Q₁, _, hRc, _, hQcard, hhit⟩ := exists_two_sided_hitting_set
    (univ : Finset V) univ_nonempty (univ : Finset P) N₁ N₂ (d * (m + 1))
    (by positivity) (by intro i _; exact subset_univ _) (by intro i _; exact subset_univ _)
    (fun i _ => hN₁ i) (fun i _ => hN₂ i)
  let E := H₀.edgeFinset ∪ (univ : Finset P).biUnion F
  let Hpre := graphOfEdges E
  have hE : E ⊆ G.edgeFinset := by
    apply union_subset (edgeFinset_mono h₀G)
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact hFG i hi
  have hpreG : Hpre ≤ G := graphOfEdges_le hE
  have h₀pre : H₀ ≤ Hpre := le_graphOfEdges subset_union_left
  have hFpre (i : P) : F i ⊆ Hpre.edgeFinset := by
    intro e he
    exact graphOfEdges_mem (hFG i he) (mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, he⟩))
  have hpreCost : Hpre.edgeFinset.card ≤ H₀.edgeFinset.card + 2 * P.card * m := by
    have hF : ((univ : Finset P).biUnion F).card ≤ 2 * P.card * m := calc
      _ ≤ ∑ i : P, (F i).card := card_biUnion_le
      _ ≤ ∑ _ : P, 2 * m := sum_le_sum (fun i _ => hFsize i)
      _ = _ := by simp [Nat.mul_comm, Nat.mul_left_comm]
    exact (graphOfEdges_card_le E).trans ((card_union_le _ _).trans (Nat.add_le_add_left hF _))
  obtain ⟨T, hTspan, hTcost⟩ := hsubset R
  let H := graphOfEdges (Hpre.edgeFinset ∪ T.edgeFinset)
  have hpreH : Hpre ≤ H := le_graphOfEdges subset_union_left
  have hTH : T ≤ H := le_graphOfEdges subset_union_right
  have hHG : H ≤ G := graphOfEdges_le (union_subset (edgeFinset_mono hpreG) (edgeFinset_mono hTspan.1))
  have hHcost : (H.edgeFinset.card : ℝ) ≤ Hpre.edgeFinset.card + T.edgeFinset.card := by
    exact_mod_cast (graphOfEdges_card_le (Hpre.edgeFinset ∪ T.edgeFinset)).trans (card_union_le Hpre.edgeFinset T.edgeFinset)
  let Q := Q₁.image (fun i : P => i.val)
  have hQ : Q.card = Q₁.card := card_image_of_injective _ Subtype.val_injective
  have hQP : Q ⊆ P := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact j.property
  have hRc' : R.card ≤ 2 * (2 * Fintype.card V / (d * (m + 1)) + 1) := by simpa using hRc
  refine ⟨H, Q, hHG, hQP, ?_, ?_, ?_⟩
  · have hh : P.card ≤ 4 * Q₁.card := by simpa using hQcard
    omega
  · have hR : (R.card : ℝ) ≤ (2 * (2 * Fintype.card V / (d * (m + 1)) + 1) : ℕ) := by exact_mod_cast hRc'
    have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hR)
      (show (0 : ℝ) ≤ C * Fintype.card V by positivity)
    have hpre : (Hpre.edgeFinset.card : ℝ) ≤ H₀.edgeFinset.card + 2 * P.card * m := by exact_mod_cast hpreCost
    linarith
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    obtain ⟨⟨r, hrR, hrN⟩, ⟨q, hqR, hqN⟩⟩ := hhit j hj
    obtain ⟨x, y, mid, hrx, hyq, hmidshort, hmissing, hpx, hyt, hsplit⟩ :=
      hatt j H hHG (h₀pre.trans hpreH) ((hFpre j).trans (edgeFinset_mono hpreH)) r hrN q hqN
    have hconnector : H.edist r q ≤ G.edist r q + 2 :=
      (edist_anti hTH).trans (hTspan.2 (r,q) (mem_product.mpr ⟨hrR,hqR⟩))
    exact route_three_segments G H (src j.val) x y (dst j.val) 6 hpx hyt
      (plus_six_between_attachments G H hHG x y r q ((h₀pre.trans hpreH) hrx.symm)
        ((h₀pre.trans hpreH) hyq.symm) hconnector) hsplit

end SlackSparsification
