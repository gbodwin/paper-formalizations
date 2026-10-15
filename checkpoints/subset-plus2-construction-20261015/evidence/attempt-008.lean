import SlackSparsification.SubsetPlusTwoConstruction

namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem captured_prefix {G H : SimpleGraph V} {s t : V} (p : G.Walk s t)
    (hcap : p.edges.toFinset ⊆ H.edgeFinset) (C : Finset V) :
    clusterEDist H s C ≤ prefixDistance p C := by
  apply Finset.le_inf
  intro i hi
  obtain ⟨hil, hic⟩ := (mem_clusterPositions p C i).mp hi
  have ht := ((p.take i).transfer H (fun e he => mem_edgeFinset.mp
    (hcap (List.mem_toFinset.mpr ((p.isSubwalk_take i).edges_subset he))))).edist_le
  rw [Walk.length_transfer, Walk.take_length, Nat.min_eq_left hil] at ht
  exact (clusterEDist_le H s C hic).trans ht

theorem captured_suffix {G H : SimpleGraph V} {s t : V} (p : G.Walk s t)
    (hcap : p.edges.toFinset ⊆ H.edgeFinset) (C : Finset V) :
    clusterEDist H t C ≤ suffixDistance p C := by
  apply Finset.le_inf
  intro i hi
  obtain ⟨_, hic⟩ := (mem_clusterPositions p C i).mp hi
  have ht := ((p.drop i).transfer H (fun e he => mem_edgeFinset.mp
    (hcap (List.mem_toFinset.mpr ((p.isSubwalk_drop i).edges_subset he))))).edist_le
  rw [Walk.length_transfer, Walk.drop_length, H.edist_comm] at ht
  exact (clusterEDist_le H t C hic).trans ht

/-- One actual purchase/rejection step. Diagonal and unreachable demands carry
no charge. For distinct endpoints, the two sets of charge labels are disjoint. -/
theorem purchase_step (G : SimpleGraph V) (d : ℕ) (cert : ClusteringCertificate G d)
    (S : Finset V) (H : SimpleGraph V) (hbase : cert.base ≤ H) (hHG : H ≤ G)
    (s : V) (hs : s ∈ S) (t : V) (ht : t ∈ S) :
    ∃ K : SimpleGraph V, ∃ Q : Finset (V × Finset V),
      H ≤ K ∧ K ≤ G ∧ Q ⊆ S ×ˢ cert.clusters ∧
      K.edgeFinset.card ≤ H.edgeFinset.card + 2 * Q.card ∧
      K.edist s t ≤ G.edist s t + 2 ∧
      ∀ q ∈ Q, clusterEDist K q.1 q.2 < clusterEDist H q.1 q.2 ∧
        clusterEDist K q.1 q.2 ≤ clusterEDist G q.1 q.2 + 2 := by
  by_cases hst : s = t
  · subst t
    exact ⟨H, ∅, le_rfl, hHG, empty_subset _, by simp, by simp, by simp⟩
  by_cases hr : G.Reachable s t
  swap
  · refine ⟨H, ∅, le_rfl, hHG, empty_subset _, by simp, ?_, by simp⟩
    simp [G.edist_eq_top_of_not_reachable hr]
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  let Cs := cert.clusters.filter fun C => (clusterPositions p C).Nonempty
  let BL := Cs.filter fun C => prefixDistance p C < clusterEDist H s C
  let BR := Cs.filter fun C => suffixDistance p C < clusterEDist H t C
  let Q := ({s} ×ˢ BL) ∪ ({t} ×ˢ BR)
  have hQcard : Q.card = BL.card + BR.card := by
    rw [card_union_of_disjoint]
    · simp
    · apply Finset.disjoint_left.mpr
      intro q hq hq'
      have h1 : q.1 = s := by simpa using (mem_product.mp hq).1
      have h2 : q.1 = t := by simpa using (mem_product.mp hq').1
      exact hst (h1.symm.trans h2)
  let cost := (missingIndices H p).card
  have hcount : cost ≤ 2 * Cs.card := by
    apply missing_count_of_certificate G d cert p hp
    intro i hi
    obtain ⟨hi, hm⟩ := mem_filter.mp hi
    exact ⟨mem_range.mp hi, fun ha => hm (hbase ha)⟩
  by_cases hbuy : cost ≤ 2 * (BL.card + BR.card)
  · let E := H.edgeFinset ∪ p.edges.toFinset
    let K := graphOfEdges E
    have hEsub : E ⊆ G.edgeFinset := by
      apply union_subset
      · exact edgeFinset_mono hHG
      · intro e he
        exact mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
    have hKH : H ≤ K := le_graphOfEdges subset_union_left
    have hKG : K ≤ G := graphOfEdges_le hEsub
    have hcap : p.edges.toFinset ⊆ K.edgeFinset := by
      intro e he
      induction e using Sym2.inductionOn with
      | _ a b =>
        apply mem_edgeFinset.mpr
        exact ⟨mem_union_right _ he, (mem_edgeFinset.mp (hEsub (mem_union_right _ he))).ne⟩
    have hcost : K.edgeFinset.card ≤ H.edgeFinset.card + cost := by
      calc
        _ ≤ E.card := graphOfEdges_card_le _
        _ = H.edgeFinset.card + (p.edges.toFinset \ H.edgeFinset).card := by
          dsimp [E]
          rw [← union_sdiff_self_eq_union (s := H.edgeFinset) (t := p.edges.toFinset), card_union_of_disjoint disjoint_sdiff_right]
        _ ≤ _ := Nat.add_le_add_left (missing_edges_card_le H p) _
    refine ⟨K, Q, hKH, hKG, ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases mem_union.mp hq with hq | hq
      · obtain ⟨hx, hC⟩ := mem_product.mp hq
        have he : q.1 = s := by simpa using hx
        exact mem_product.mpr ⟨he ▸ hs, (mem_filter.mp (mem_filter.mp hC).1).1⟩
      · obtain ⟨hx, hC⟩ := mem_product.mp hq
        have he : q.1 = t := by simpa using hx
        exact mem_product.mpr ⟨he ▸ ht, (mem_filter.mp (mem_filter.mp hC).1).1⟩
    · rw [hQcard]
      exact hcost.trans (Nat.add_le_add_left hbuy _)
    · rw [captured_path_distance hKG p hp hcap]
      exact le_add_right le_rfl
    · intro q hq
      rcases mem_union.mp hq with hq | hq
      · obtain ⟨hx, hC⟩ := mem_product.mp hq
        have he : q.1 = s := by simpa using hx
        rw [he]
        obtain ⟨hvisit, himp⟩ := mem_filter.mp hC
        obtain ⟨hc, hv⟩ := mem_filter.mp hvisit
        have hpre := captured_prefix p hcap q.2
        exact ⟨hpre.trans_lt himp, hpre.trans (prefix_le_global_add_two G p hp q.2
          (diameter_mono cert.base_le _ (cert.diameter _ hc)) hv)⟩
      · obtain ⟨hx, hC⟩ := mem_product.mp hq
        have he : q.1 = t := by simpa using hx
        rw [he]
        obtain ⟨hvisit, himp⟩ := mem_filter.mp hC
        obtain ⟨hc, hv⟩ := mem_filter.mp hvisit
        have hsuf := captured_suffix p hcap q.2
        exact ⟨hsuf.trans_lt himp, hsuf.trans (suffix_le_global_add_two G p hp q.2
          (diameter_mono cert.base_le _ (cert.diameter _ hc)) hv)⟩
  · refine ⟨H, ∅, le_rfl, hHG, empty_subset _, by simp, ?_, by simp⟩
    apply rejected_path_satisfied G H p hp Cs
    · intro C hC
      exact diameter_mono hbase C (cert.diameter C (mem_filter.mp hC).1)
    · intro C hC
      exact (mem_filter.mp hC).2
    · exact hcount
    · exact Nat.lt_of_not_ge hbuy

end SlackSparsification.SubsetPlusTwo
