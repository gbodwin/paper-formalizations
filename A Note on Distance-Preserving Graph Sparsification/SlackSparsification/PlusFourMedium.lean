import SlackSparsification.Attachments
import SlackSparsification.PairConnector
import Mathlib.Tactic

/-! Actual medium-demand construction for Theorem 12. The finite hitting
set, prefix/suffix purchases, and shortest-candidate connector are internal. -/
namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

/-- At least a quarter of medium demands obtain additive error four. -/
theorem exists_plus_four_medium (G H₀ : SimpleGraph V) (h₀G : H₀ ≤ G)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (d m K : ℕ) (hd : 0 < d)
    (hdegree : ∀ u v, G.Adj u v → ¬H₀.Adj u v → 3 * d ≤ H₀.degree u)
    (hmedium : ∀ i ∈ P, 2 * m < (missingIndices H₀ (p i)).card ∧
      (missingIndices H₀ (p i)).card ≤ K) :
    ∃ (H : SimpleGraph V) (Q : Finset D), H ≤ G ∧ Q ⊆ P ∧ P.card ≤ 4 * Q.card ∧
      H.edgeFinset.card ≤ H₀.edgeFinset.card + 2 * P.card * m +
        (2 * (2 * Fintype.card V / (d * (m + 1)) + 1)) ^ 2 * K ∧
      ∀ i ∈ Q, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 4 := by
  classical
  choose F N₁ N₂ hFG hFsize hN₁ hN₂ hatt using fun i : P =>
    exists_path_attachments G H₀ h₀G d m hdegree (p i.val) (hp i.val) (hmedium i.val i.property).1
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
  obtain ⟨H, hpreH, hHG, hHcost, hHsat⟩ := exists_pair_connector G Hpre hpreG R K
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
  · have hr := Nat.mul_le_mul_right K (Nat.pow_le_pow_left hRc' 2)
    omega
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    obtain ⟨⟨r, hrR, hrN⟩, ⟨q, hqR, hqN⟩⟩ := hhit j hj
    obtain ⟨x, y, mid, hrx, hyq, hmidshort, hmissing, hpx, hyt, hsplit⟩ :=
      hatt j H hHG (h₀pre.trans hpreH) ((hFpre j).trans (edgeFinset_mono hpreH)) r hrN q hqN
    have hmissing' : (mid.edges.toFinset \ Hpre.edgeFinset).card ≤ K := by
      apply le_trans _ (hmissing.trans (hmedium j.val j.property).2)
      apply card_le_card
      exact sdiff_subset_sdiff subset_rfl (edgeFinset_mono h₀pre)
    exact route_three_segments G H (src j.val) x y (dst j.val) 4 hpx hyt
      (hHsat r hrR q hqR x y mid hmidshort (h₀pre hrx) (h₀pre hyq) hmissing') hsplit

end SlackSparsification
