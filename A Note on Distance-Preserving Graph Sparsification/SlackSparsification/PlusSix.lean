import SlackSparsification.PlusSixRouting
import SlackSparsification.Hitting
import SlackSparsification.PairConnector
import Mathlib.Tactic

/-! Actual +6 slack graph, conditional only on the uniform cited Theorem 10
premise. Short paths are bought outright; long paths use the existing ordered
prefix/suffix construction and deterministic two-sided hitting theorem. -/
namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
variable {V D : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [DecidableEq D]
attribute [local instance] Classical.propDecidable

/-- Conditional Theorem 11 with quarter coverage and an explicit integer
budget. The subset-spanner premise is invoked only on the constructed roots. -/
theorem exists_plus_six_slack_paths (G : SimpleGraph V) (C : ℝ) (hC : 0 < C)
    (hsubset : UniformSubsetPlusTwo G C)
    (src dst : D → V) (p : ∀ i, G.Walk (src i) (dst i))
    (hp : ∀ i, (p i).length = G.dist (src i) (dst i))
    (P : Finset D) (d m : ℕ) (hd : 0 < d) :
    ∃ (H : SimpleGraph V) (Q : Finset D), H ≤ G ∧ Q ⊆ P ∧ P.card ≤ 4 * Q.card ∧
      (H.edgeFinset.card : ℝ) ≤
        (3 * Fintype.card V * d + 2 * P.card * m : ℕ) +
          C * Fintype.card V * Real.sqrt
            (2 * (2 * Fintype.card V / (d * (m + 1)) + 1) : ℕ) ∧
      ∀ i ∈ Q, H.edist (src i) (dst i) ≤ G.edist (src i) (dst i) + 6 := by
  classical
  obtain ⟨H₀, h₀G, h₀size, hdegree⟩ := exists_initialization G (3 * d)
  let A := P.filter fun i => (missingIndices H₀ (p i)).card ≤ 2 * m
  let B := P \ A
  have hAP : A ⊆ P := filter_subset _ _
  have hBP : B ⊆ P := sdiff_subset
  have hlong (i : B) : 2 * m < (missingIndices H₀ (p i.val)).card := by
    obtain ⟨hiP, hiA⟩ := mem_sdiff.mp i.property
    by_contra hn
    exact hiA (mem_filter.mpr ⟨hiP, by omega⟩)
  choose F N₁ N₂ hFG hFsize hN₁ hN₂ hatt using fun i : B =>
    exists_path_attachments G H₀ h₀G d m hdegree (p i.val) (hp i.val) (hlong i)
  obtain ⟨R, Q₁, _, hRc, _, hQcard, hhit⟩ := exists_two_sided_hitting_set
    (univ : Finset V) univ_nonempty (univ : Finset B) N₁ N₂ (d * (m + 1))
    (by positivity) (by intro i _; exact subset_univ _) (by intro i _; exact subset_univ _)
    (fun i _ => hN₁ i) (fun i _ => hN₂ i)
  obtain ⟨K, hKG, hKcost, hKsat⟩ := hsubset R
  let Fshort := fun i => (p i).edges.toFinset \ H₀.edgeFinset
  let Eshort := A.biUnion Fshort
  let Elong := (univ : Finset B).biUnion F
  let Epre := H₀.edgeFinset ∪ (Eshort ∪ Elong)
  let E := Epre ∪ K.edgeFinset
  let H := graphOfEdges E
  have hshortG : Eshort ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact mem_edgeFinset.mpr ((p i).edges_subset_edgeSet (List.mem_toFinset.mp (mem_sdiff.mp hi).1))
  have hlongG : Elong ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact hFG i hi
  have hpreG : Epre ⊆ G.edgeFinset :=
    union_subset (edgeFinset_mono h₀G) (union_subset hshortG hlongG)
  have hEG : E ⊆ G.edgeFinset := union_subset hpreG (edgeFinset_mono hKG)
  have hHG : H ≤ G := graphOfEdges_le hEG
  have h₀H : H₀ ≤ H := le_graphOfEdges (subset_union_left.trans subset_union_left)
  have hKH : K ≤ H := le_graphOfEdges subset_union_right
  have hshortH : Eshort ⊆ H.edgeFinset := by
    intro e he
    exact graphOfEdges_mem (hshortG he)
      (mem_union_left _ (mem_union_right _ (mem_union_left _ he)))
  have hFH (i : B) : F i ⊆ H.edgeFinset := by
    intro e he
    exact graphOfEdges_mem (hFG i he)
      (mem_union_left _ (mem_union_right _ (mem_union_right _
        (mem_biUnion.mpr ⟨i, mem_univ _, he⟩))))
  have hshortCost : Eshort.card ≤ A.card * (2 * m) := calc
    _ ≤ ∑ i ∈ A, (Fshort i).card := card_biUnion_le
    _ ≤ ∑ _ ∈ A, 2 * m := sum_le_sum (fun i hi =>
      (missing_edges_card_le H₀ (p i)).trans (mem_filter.mp hi).2)
    _ = _ := by simp
  have hlongCost : Elong.card ≤ B.card * (2 * m) := calc
    _ ≤ ∑ i : B, (F i).card := card_biUnion_le
    _ ≤ ∑ _ : B, 2 * m := sum_le_sum (fun i _ => hFsize i)
    _ = _ := by simp
  have hAB : B.card + A.card = P.card := card_sdiff_add_card_eq_card hAP
  have hpreCost : Epre.card ≤ 3 * Fintype.card V * d + 2 * P.card * m := by
    have hu := card_union_le H₀.edgeFinset (Eshort ∪ Elong)
    have hu' := card_union_le Eshort Elong
    have he : A.card * (2 * m) + B.card * (2 * m) = 2 * P.card * m := by
      nlinarith only [congrArg (fun n => n * (2 * m)) hAB]
    nlinarith only [hu, hu', hshortCost, hlongCost, h₀size, he]
  let Qlong := Q₁.image (fun i : B => i.val)
  let Q := A ∪ Qlong
  have hQlB : Qlong ⊆ B := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact j.property
  have hQl : Qlong.card = Q₁.card := card_image_of_injective _ Subtype.val_injective
  have hdis : Disjoint A Qlong := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiQ
    exact (mem_sdiff.mp (hQlB hiQ)).2 hiA
  have hQ : Q.card = A.card + Qlong.card := card_union_of_disjoint hdis
  have hRc' : R.card ≤ 2 * (2 * Fintype.card V / (d * (m + 1)) + 1) := by simpa using hRc
  refine ⟨H, Q, hHG, union_subset hAP (hQlB.trans hBP), ?_, ?_, ?_⟩
  · have hh : B.card ≤ 4 * Q₁.card := by simpa using hQcard
    omega
  · have hc : H.edgeFinset.card ≤ Epre.card + K.edgeFinset.card :=
      (graphOfEdges_card_le E).trans (card_union_le _ _)
    have hc' : (H.edgeFinset.card : ℝ) ≤ Epre.card + K.edgeFinset.card := by exact_mod_cast hc
    have hp' : (Epre.card : ℝ) ≤ (3 * Fintype.card V * d + 2 * P.card * m : ℕ) := by
      exact_mod_cast hpreCost
    have hr' : (R.card : ℝ) ≤ (2 * (2 * Fintype.card V / (d * (m + 1)) + 1) : ℕ) := by
      exact_mod_cast hRc'
    have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr')
      (show 0 ≤ C * Fintype.card V by positivity)
    linarith
  · intro i hi
    rcases mem_union.mp hi with hi | hi
    · have hdist : H.edist (src i) (dst i) = G.edist (src i) (dst i) := by
        apply captured_path_distance hHG (p i) (hp i)
        apply captured_edges_of_purchase h₀H
        intro e he
        exact hshortH (mem_biUnion.mpr ⟨i, hi, he⟩)
      rw [hdist]
      exact le_self_add
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      obtain ⟨⟨r, hrR, hrN⟩, ⟨q, hqR, hqN⟩⟩ := hhit j hj
      obtain ⟨x, y, _, hrx, hyq, _, _, hpx, hyt, hsplit⟩ :=
        hatt j H hHG h₀H (hFH j) r hrN q hqN
      exact plus_six_from_subset_connector G H K hHG hKH (src j.val) x y (dst j.val) r q
        (h₀H hrx) (h₀H hyq) (hKsat r hrR q hqR) hpx hyt hsplit

end SlackSparsification
