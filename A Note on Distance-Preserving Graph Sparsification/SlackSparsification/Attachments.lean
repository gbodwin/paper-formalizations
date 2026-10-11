import SlackSparsification.PrefixSuffix
import SlackSparsification.Initialization
import Mathlib.Tactic

/-! Actual prefix/suffix purchases, with ordered attachment points. More
than 2m missing edges is the long case; other paths can be bought outright. -/
namespace SlackSparsification
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A purchased difference together with the initial graph captures the path. -/
theorem captured_edges_of_purchase {G H₀ H : SimpleGraph V} (h₀H : H₀ ≤ H)
    {s t : V} (p : G.Walk s t)
    (hbuy : p.edges.toFinset \ H₀.edgeFinset ⊆ H.edgeFinset) :
    p.edges.toFinset ⊆ H.edgeFinset := by
  intro e he
  by_cases he₀ : e ∈ H₀.edgeFinset
  · exact edgeFinset_mono h₀H he₀
  · exact hbuy (mem_sdiff.mpr ⟨he, he₀⟩)

/-- Spend at most 2m edges on a path. Each of two large neighborhoods
then supplies an ordered attachment, and the intervening shortest subpath
has no more missing edges than the original path. -/
theorem exists_path_attachments (G H₀ : SimpleGraph V) (h₀G : H₀ ≤ G)
    (d m : ℕ)
    (hdegree : ∀ u v, G.Adj u v → ¬H₀.Adj u v → 3 * d ≤ H₀.degree u)
    {s t : V} (p : G.Walk s t) (hp : p.length = G.dist s t)
    (hlong : 2 * m < (missingIndices H₀ p).card) :
    ∃ (F : Finset (Sym2 V)) (N₁ N₂ : Finset V), F ⊆ G.edgeFinset ∧ F.card ≤ 2 * m ∧
      d * (m + 1) ≤ N₁.card ∧ d * (m + 1) ≤ N₂.card ∧
      ∀ (H : SimpleGraph V), H ≤ G → H₀ ≤ H → F ⊆ H.edgeFinset →
        ∀ r ∈ N₁, ∀ q ∈ N₂, ∃ (x y : V) (mid : G.Walk x y),
          H₀.Adj r x ∧ H₀.Adj y q ∧ mid.length = G.dist x y ∧
          (mid.edges.toFinset \ H₀.edgeFinset).card ≤ (missingIndices H₀ p).card ∧
          H.edist s x = G.edist s x ∧ H.edist y t = G.edist y t ∧
          G.edist s x + G.edist x y + G.edist y t = G.edist s t := by
  classical
  let M := missingIndices H₀ p
  obtain ⟨a, b, ha, hb, hab, hac, hbc, haN, hbN⟩ := ordered_missing_cuts M m hlong
  have haL : a < p.length := mem_range.mp (missingIndices_subset H₀ p ha)
  have hbL : b < p.length := mem_range.mp (missingIndices_subset H₀ p hb)
  let I₁ := M.filter (· ≤ a)
  let I₂ := (M.filter (b ≤ ·)).image (· + 1)
  let N₁ := I₁.biUnion fun j => H₀.neighborFinset (p.getVert j)
  let N₂ := I₂.biUnion fun j => H₀.neighborFinset (p.getVert j)
  let F₁ := (p.take a).edges.toFinset \ H₀.edgeFinset
  let F₂ := (p.drop (b + 1)).edges.toFinset \ H₀.edgeFinset
  let F := F₁ ∪ F₂
  have hFG : F ⊆ G.edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_edgeFinset.mpr ((p.take a).edges_subset_edgeSet (List.mem_toFinset.mp (mem_sdiff.mp he).1))
    · exact mem_edgeFinset.mpr ((p.drop (b + 1)).edges_subset_edgeSet (List.mem_toFinset.mp (mem_sdiff.mp he).1))
  have hF₁ : F₁.card ≤ m := by
    have h := missing_edges_card_le H₀ (p.take a)
    rw [missingIndices_take H₀ p a haL.le] at h
    exact h.trans_eq hac
  have hF₂ : F₂.card ≤ m := by
    have h := (missing_edges_card_le H₀ (p.drop (b + 1))).trans (missingIndices_drop_card H₀ p (b + 1))
    have he : (M.filter (b + 1 ≤ ·)) = M.filter (b < ·) := by ext i; simp [Nat.lt_iff_add_one_le]
    change F₂.card ≤ (M.filter (b + 1 ≤ ·)).card at h
    exact (he ▸ h).trans_eq hbc
  have hI₂c : I₂.card = m + 1 := by
    rw [show I₂ = (M.filter (b ≤ ·)).image (· + 1) from rfl,
      card_image_of_injective _ (by intro i j h; omega)]
    exact hbN
  have hN₁ : d * (m + 1) ≤ N₁.card := by
    have hc := path_vertex_neighborhood_count G H₀ h₀G p hp I₁
      (by intro j hj; exact (mem_range.mp (missingIndices_subset H₀ p (mem_filter.mp hj).1)).le)
      (3 * d) (by
        intro j hj
        have hm := mem_filter.mp (mem_filter.mp hj).1
        exact hdegree _ _ (p.adj_getVert_succ (mem_range.mp hm.1)) hm.2)
    change 3 * d * I₁.card ≤ 3 * N₁.card at hc
    have hi : I₁.card = m + 1 := haN
    nlinarith
  have hN₂ : d * (m + 1) ≤ N₂.card := by
    have hc := path_vertex_neighborhood_count G H₀ h₀G p hp I₂ (by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      have hiL := mem_range.mp (missingIndices_subset H₀ p (mem_filter.mp hi).1)
      omega) (3 * d) (by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
        have hm := mem_filter.mp (mem_filter.mp hi).1
        exact hdegree _ _ (p.adj_getVert_succ (mem_range.mp hm.1)).symm
          (fun h => hm.2 h.symm))
    change 3 * d * I₂.card ≤ 3 * N₂.card at hc
    nlinarith
  refine ⟨F, N₁, N₂, hFG, (card_union_le F₁ F₂).trans (by omega), hN₁, hN₂, ?_⟩
  intro H hHG h₀H hFH r hr q hq
  obtain ⟨j, hj, hrj⟩ := mem_biUnion.mp hr
  obtain ⟨k, hk, hqk⟩ := mem_biUnion.mp hq
  have hja : j ≤ a := (mem_filter.mp hj).2
  obtain ⟨i, hi, hik⟩ := mem_image.mp hk
  have hbi : b ≤ i := (mem_filter.mp hi).2
  have hiL := mem_range.mp (missingIndices_subset H₀ p (mem_filter.mp hi).1)
  have hjk : j ≤ k := by omega
  have hkL : k ≤ p.length := by omega
  have hjL : j ≤ p.length := by omega
  have hpre : (p.take a).edges.toFinset ⊆ H.edgeFinset :=
    captured_edges_of_purchase h₀H _ (fun _ he => hFH (mem_union_left _ he))
  have hsuf : (p.drop (b + 1)).edges.toFinset ⊆ H.edgeFinset :=
    captured_edges_of_purchase h₀H _ (fun _ he => hFH (mem_union_right _ he))
  have hpx : H.edist s (p.getVert j) = G.edist s (p.getVert j) :=
    captured_path_distance hHG (p.take j) (length_eq_dist_of_subwalk hp (p.isSubwalk_take j)) (by
      intro e he
      exact hpre (List.mem_toFinset.mpr ((p.take_isSubwalk_take hja).edges_subset (List.mem_toFinset.mp he))))
  have hyt : H.edist (p.getVert k) t = G.edist (p.getVert k) t :=
    captured_path_distance hHG (p.drop k) (length_eq_dist_of_subwalk hp (p.isSubwalk_drop k)) (by
      intro e he
      exact hsuf (List.mem_toFinset.mpr ((p.drop_isSubwalk_drop (show b + 1 ≤ k by omega)).edges_subset (List.mem_toFinset.mp he))))
  have he : (p.drop j).getVert (k - j) = p.getVert k := by
    rw [Walk.drop_getVert, Nat.add_sub_of_le hjk]
  let mid := ((p.drop j).take (k - j)).copy rfl he
  have hsub : mid.IsSubwalk p := by
    simpa [mid] using (((p.drop j).isSubwalk_take (k - j)).trans (p.isSubwalk_drop j)).copy rfl he rfl rfl
  have hmissing : (mid.edges.toFinset \ H₀.edgeFinset).card ≤ M.card := by
    apply le_trans _ (missing_edges_card_le H₀ p)
    apply card_le_card
    intro e hm
    exact mem_sdiff.mpr ⟨List.mem_toFinset.mpr (hsub.edges_subset (List.mem_toFinset.mp (mem_sdiff.mp hm).1)), (mem_sdiff.mp hm).2⟩
  refine ⟨p.getVert j, p.getVert k, mid, (show H₀.Adj (p.getVert j) r by simpa using hrj).symm,
    (by simpa using hqk), length_eq_dist_of_subwalk hp hsub, hmissing, hpx, hyt, ?_⟩
  have hs := shortest_split p hp j hjL
  have ht := shortest_split (p.drop j) (length_eq_dist_of_subwalk hp (p.isSubwalk_drop j))
    (k - j) (by simp only [Walk.drop_length]; omega)
  rw [he] at ht
  calc
    _ = G.edist s (p.getVert j) + (G.edist (p.getVert j) (p.getVert k) + G.edist (p.getVert k) t) := by ac_rfl
    _ = _ := by rw [ht, hs]

end SlackSparsification
