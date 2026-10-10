import GreedyShortcuts.ChainFirst
import GreedyShortcuts.NormalizedValidity

/-! Instantiate earliest-entry normalization on actual disjoint directed
chains with their mapped forward supershortcut witnesses. -/
namespace GreedyShortcuts.ChainNormalization

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainUnion ChainFirst
open NormalizedReachability NormalizedValidity
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable {G : V → V → Prop}

theorem index_le_of_reachable (hG : Acyclic G) (C : Chain G)
    (i j : Fin C.length) (hr : Reachable G (C.node i) (C.node j)) : i ≤ j := by
  by_contra hn
  have hj := lt_of_not_ge hn
  have he := (acyclic_iff_reachable_antisymm G).mp hG _ _ hr (C.forward j i hj)
  have hij := C.injective he
  exact (ne_of_lt hj) hij.symm

def unionEdges (C : I → Chain G) {K : ℕ} (W : ∀ c,PathWitness (C c).length K) :
    Finset (V × V) := Finset.univ.biUnion (fun c => mappedEdges (C c) (W c))

theorem local_subset (C : I → Chain G) {K : ℕ} (W : ∀ c,PathWitness (C c).length K) (c : I) :
    mappedEdges (C c) (W c) ⊆ unionEdges C W := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,he⟩

theorem union_subset (C : I → Chain G) {K : ℕ} (W : ∀ c,PathWitness (C c).length K) :
    unionEdges C W ⊆ candidates G := by
  intro e he
  obtain ⟨c,hc,he⟩ := Finset.mem_biUnion.mp he
  exact mappedEdges_subset (C c) (W c) he

theorem map_same_label (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    (c : I) {i j : Fin (C c).length} (p : DWalk i j) :
    ∀ d ∈ (p.map (DirectedMap.hom (C c).node (C c).injective)).darts,
      label C d.fst = label C d.snd := by
  induction p with
  | nil => simp
  | @cons i k j ha p ih =>
    intro d hd
    simp only [Walk.map_cons,Walk.darts_cons,List.mem_cons] at hd
    rcases hd with rfl | hd
    · simpa [DirectedMap.hom] using (label_node C hdisj c i).trans (label_node C hdisj c k).symm
    · exact ih d hd

/-- The concrete union provides internal walks for all forward same-chain
pairs, which is the hypothesis needed by earliest-entry normalization. -/
theorem internal_walk (hG : Acyclic G) (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    {K : ℕ} (W : ∀ c,PathWitness (C c).length K) (u v : V)
    (hr : Reachable (augment G (unionEdges C W)) u v)
    (hcol : label C u = label C v) (hc : label C v ≠ none) :
    ∃ p : DWalk u v,Allowed (augment G (unionEdges C W)) p ∧
      ∀ d ∈ p.darts,label C d.fst = label C d.snd := by
  classical
  obtain ⟨c,hcv⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨i,hi,hiu⟩ := Finset.mem_image.mp (mem_of_label C (hcol.trans hcv))
  obtain ⟨j,hj,hjv⟩ := Finset.mem_image.mp (mem_of_label C hcv)
  have hr' := (reachable_augment_iff G _ (union_subset C W) u v).mp hr
  have hij := index_le_of_reachable hG (C c) i j (by simpa only [hiu,hjv] using hr')
  subst u
  subst v
  obtain ⟨p,hp,hp4⟩ := (W c).short i j hij
  let q := p.map (DirectedMap.hom (C c).node (C c).injective)
  have hq : Allowed (augment G (unionEdges C W)) q :=
    DirectedMap.allowed_map (C c).node (C c).injective
      (fun a b hab => Or.inr (local_subset C W c (DirectedMap.mem_edges _ _ hab))) p hp
  exact ⟨q,hq,map_same_label C hdisj c p⟩

/-- Earliest-entry valid walks really exist for every originally reachable
pair after the explicitly constructed chain supershortcut union. -/
theorem reachable_normalized_iff (hG : Acyclic G) (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    {K : ℕ} (W : ∀ c,PathWitness (C c).length K) (s t : V) :
    Reachable (filtered (augment G (unionEdges C W)) (label C) (first C) s) s t ↔ Reachable G s t := by
  have hH := union_subset C W
  rw [reachable_filtered_iff (acyclic_augment hG hH) (label C) (first C) ?_ (internal_walk hG C hdisj W)]
  · exact reachable_augment_iff G _ hH s t
  · intro s v hr hc
    obtain ⟨hfs,hfv,hfc⟩ := first_spec C hdisj s v ((reachable_augment_iff G _ hH s v).mp hr) hc
    exact ⟨reachable_augment G _ hfs,reachable_augment G _ hfv,hfc⟩

theorem union_card_le (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    {K : ℕ} (W : ∀ c,PathWitness (C c).length K) :
    (unionEdges C W).card ≤ K*Fintype.card V := by
  calc
    _ ≤ ∑ c,(mappedEdges (C c) (W c)).card := Finset.card_biUnion_le
    _ ≤ ∑ c,K*(C c).length := Finset.sum_le_sum (fun c _ =>
      (DirectedMap.edges_card_le _ _).trans (W c).card_le)
    _ = K*∑ c,(C c).length := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (disjoint_length_sum C hdisj)

/-- Concrete existence and chain-contiguity of the source's valid paths after
chain preprocessing. The separate shortest-valid-path progress lemma is not
used or asserted. -/
theorem valid_paths_exist (hG : Acyclic G) (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support))
    {K : ℕ} (W : ∀ c,PathWitness (C c).length K) {s t : V} (hr : Reachable G s t) :
    ∃ p : DWalk s t,Allowed (filtered (augment G (unionEdges C W)) (label C) (first C) s) p ∧
      p.IsPath ∧ ∀ i j k,i ≤ j → j ≤ k → k ≤ p.length → ∀ c : I,
        label C (p.getVert i) = some c → label C (p.getVert k) = some c →
          label C (p.getVert j) = some c := by
  have hH := union_subset C W
  apply exists_valid_walk (acyclic_augment hG hH) (label C) (first C) ?_
    (first_constant C) (internal_walk hG C hdisj W) (reachable_augment G _ hr)
  intro s v hv hc
  obtain ⟨hfs,hfv,hfc⟩ := first_spec C hdisj s v ((reachable_augment_iff G _ hH s v).mp hv) hc
  exact ⟨reachable_augment G _ hfs,reachable_augment G _ hfv,hfc⟩

end GreedyShortcuts.ChainNormalization
