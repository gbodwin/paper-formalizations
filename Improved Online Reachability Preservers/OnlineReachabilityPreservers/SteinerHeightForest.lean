import OnlineReachabilityPreservers.SteinerHeightEmbedding

/-! Join the inward and outward height templates at each original root. -/

namespace OnlineReachabilityPreservers

open Finset

abbrev HeightForestVertex (V : Type*) (height : ℕ) := V ×ₗ (Bool ×ₗ HeightNode V height)

variable {V : Type*} {height : ℕ}

def heightForestRoot (v : HeightForestVertex V height) : V := (ofLex v).1

def heightForestSide (v : HeightForestVertex V height) : Bool := (ofLex (ofLex v).2).1

def heightForestHistory (v : HeightForestVertex V height) : HeightNode V height := (ofLex (ofLex v).2).2

def heightForestLabel (v : HeightForestVertex V height) : V :=
  heightLabel (heightForestRoot v) (heightForestHistory v)

def heightCopy (root : V) (outward : Bool) : HeightNode V height ↪ HeightForestVertex V height :=
  ⟨fun node => toLex (root, toLex (outward, node)),
    fun _ _ eq => congrArg heightForestHistory eq⟩

@[simp]
theorem heightForestRoot_copy (root : V) (outward : Bool) (node : HeightNode V height) :
    heightForestRoot (heightCopy root outward node) = root := rfl
@[simp]
theorem heightForestSide_copy (root : V) (outward : Bool) (node : HeightNode V height) :
    heightForestSide (heightCopy root outward node) = outward := rfl
@[simp]
theorem heightForestHistory_copy (root : V) (outward : Bool) (node : HeightNode V height) :
    heightForestHistory (heightCopy root outward node) = node := rfl
@[simp]
theorem heightForestLabel_copy (root : V) (outward : Bool) (node : HeightNode V height) :
    heightForestLabel (heightCopy root outward node) = heightLabel root node := rfl

/-- The free directed attachment between the two copies at one root. -/
def heightForestRootLink (root : V) (height : ℕ) :
    HeightForestVertex V height × HeightForestVertex V height :=
  (heightCopy root false heightRoot, heightCopy root true heightRoot)

def sourceLeaf (s : V) (a : HeightForestVertex V height) : Prop :=
  heightForestSide a = false ∧ (heightForestHistory a).val.length = height ∧ heightForestLabel a = s

def sinkLeaf (t : V) (a : HeightForestVertex V height) : Prop :=
  heightForestSide a = true ∧ (heightForestHistory a).val.length = height ∧ heightForestLabel a = t

instance [DecidableEq V] (s : V) (a : HeightForestVertex V height) : Decidable (sourceLeaf s a) := by
  unfold sourceLeaf
  infer_instance

instance [DecidableEq V] (t : V) (a : HeightForestVertex V height) : Decidable (sinkLeaf t a) := by
  unfold sinkLeaf
  infer_instance

theorem heightForestVertex_card_le (V : Type*) [Fintype V] [Nonempty V] (height : ℕ) :
    Fintype.card (HeightForestVertex V height) ≤
      (Fintype.card V * 2) * ((height + 1) * Fintype.card V ^ height) := by
  simp only [HeightForestVertex, Fintype.card_lex, Fintype.card_prod, Fintype.card_bool]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (Fintype.card V * 2) (heightNode_card_le V height)

private theorem reach_map_height {A B : Type*} (f : A ↪ B) {H : Arcs A} {s t : A}
    (path : Reach H s t) : Reach (H.map (f.prodMap f)) (f s) (f t) := by
  induction path with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (mem_map_of_mem _ e)

variable [LinearOrder V] [Fintype V]

/-- Select two inward template subgraphs, with the second interpreted as
outward in the reversed graph, and join them at their common root. -/
def joinHeightCopies (root : V) (left right : Arcs (HeightNode V height)) : Arcs (HeightForestVertex V height) :=
  left.map ((heightCopy root false).prodMap (heightCopy root false)) ∪
    (reverseArcs right).map ((heightCopy root true).prodMap (heightCopy root true)) ∪
    {heightForestRootLink root height}

def heightForest (G : Arcs V) (height : ℕ) : Arcs (HeightForestVertex V height) :=
  univ.biUnion fun root =>
    joinHeightCopies root (inwardHeightTree G root height) (inwardHeightTree (reverseArcs G) root height)

theorem joinHeightCopies_sub {G : Arcs V} {root : V} {L R : Arcs (HeightNode V height)}
    (hL : L ⊆ inwardHeightTree G root height) (hR : R ⊆ inwardHeightTree (reverseArcs G) root height) :
    joinHeightCopies root L R ⊆ heightForest G height := by
  intro e he
  refine mem_biUnion.mpr ⟨root, mem_univ _, ?_⟩
  exact (Finset.union_subset_union (Finset.union_subset_union
    (map_subset_map.mpr hL) (map_subset_map.mpr (reverseArcs_mono hR))) Subset.rfl) he

omit [Fintype V] in
theorem joinHeightCopies_route {root : V} {L R : Arcs (HeightNode V height)}
    {a b : HeightNode V height} (inward : Reach L a heightRoot) (outward : Reach R b heightRoot) :
    Reach (joinHeightCopies root L R) (heightCopy root false a) (heightCopy root true b) := by
  have first := reach_map_height (heightCopy root false) inward
  have second := reach_map_height (heightCopy root true) (reach_reverseArcs.mpr outward)
  have hL : L.map ((heightCopy root false).prodMap (heightCopy root false)) ⊆
      joinHeightCopies root L R := fun _ e => mem_union_left _ (mem_union_left _ e)
  have hR : (reverseArcs R).map ((heightCopy root true).prodMap (heightCopy root true)) ⊆
      joinHeightCopies root L R := fun _ e => mem_union_left _ (mem_union_right _ e)
  have central : heightForestRootLink root height ∈ joinHeightCopies root L R :=
    mem_union_right _ (mem_singleton_self _)
  exact ((reach_mono hL first).tail central).trans (reach_mono hR second)

theorem heightForest_edge_spec {G : Arcs V} {a b : HeightForestVertex V height}
    (he : Edge (heightForest G height) a b) :
    heightForestRoot a = heightForestRoot b ∧ Reach G (heightForestLabel a) (heightForestLabel b) := by
  obtain ⟨root, _, present⟩ := mem_biUnion.mp he
  rcases mem_union.mp present with lr | central
  · rcases mem_union.mp lr with left | right
    · obtain ⟨e, inTree, eq⟩ := mem_map.mp left
      have first : heightCopy root false e.1 = a := congrArg Prod.fst eq
      have last : heightCopy root false e.2 = b := congrArg Prod.snd eq
      rw [← first, ← last]
      exact ⟨rfl, inwardHeightTree_edge_reach inTree⟩
    · obtain ⟨e, inTree, eq⟩ := mem_map.mp right
      have first : heightCopy root true e.1 = a := congrArg Prod.fst eq
      have last : heightCopy root true e.2 = b := congrArg Prod.snd eq
      rw [← first, ← last]
      exact ⟨rfl, reach_reverseArcs.mp (inwardHeightTree_edge_reach (edge_reverseArcs.mp inTree))⟩
  · have eq := mem_singleton.mp central
    have first : a = heightCopy root false heightRoot := congrArg Prod.fst eq
    have last : b = heightCopy root true heightRoot := congrArg Prod.snd eq
    rw [first, last]
    exact ⟨rfl, .refl⟩

def heightForestWeight (G : Arcs V) (e : HeightForestVertex V height × HeightForestVertex V height) : ℕ :=
  hops G (heightForestLabel e.1) (heightForestLabel e.2)

def heightForestServes (links : Arcs (HeightForestVertex V height)) (d : V × V) : Prop :=
  ∃ a b, sourceLeaf d.1 a ∧ sinkLeaf d.2 b ∧ Reach links a b

theorem heightForest_reach_spec {G : Arcs V} {links : Arcs (HeightForestVertex V height)}
    (sub : links ⊆ heightForest G height) {a b : HeightForestVertex V height} (r : Reach links a b) :
    heightForestRoot a = heightForestRoot b ∧ Reach G (heightForestLabel a) (heightForestLabel b) := by
  induction r with
  | refl => exact ⟨rfl, .refl⟩
  | tail _ e ih =>
    have next := heightForest_edge_spec (sub e)
    exact ⟨ih.1.trans next.1, ih.2.trans next.2⟩

private theorem hops_reverse_eq {G : Arcs V} {s t : V} (reachable : Reach G s t) :
    hops (reverseArcs G) t s = hops G s t := by
  obtain ⟨forward, findForward⟩ := routePath_succeeds.mpr reachable
  obtain ⟨backward, findBackward⟩ := routePath_succeeds.mpr (reach_reverseArcs.mpr reachable)
  apply le_antisymm
  · rw [← routePath_length_eq_hops findForward]
    simpa using hops_le_walk (routePath_some findForward).1.reverse
  · rw [← routePath_length_eq_hops findBackward]
    simpa using hops_le_walk (routePath_some findBackward).1.reverse

private theorem sum_union_weight_le {A : Type*} [DecidableEq A] (P Q : Finset A) (weight : A → ℕ) :
    (∑ e ∈ P ∪ Q, weight e) ≤ (∑ e ∈ P, weight e) + ∑ e ∈ Q, weight e := by
  rw [← Finset.sum_union_inter]
  exact Nat.le_add_right _ _

theorem joinHeightCopies_weight_le {G : Arcs V} {root : V} {L R : Arcs (HeightNode V height)}
    (hR : R ⊆ inwardHeightTree (reverseArcs G) root height) :
    (∑ e ∈ joinHeightCopies root L R, heightForestWeight G e) ≤
      (∑ e ∈ L, heightLinkWeight G root e) +
        ∑ e ∈ R, heightLinkWeight (reverseArcs G) root e := by
  let L' := L.map ((heightCopy root false).prodMap (heightCopy root false))
  let R' := (reverseArcs R).map ((heightCopy root true).prodMap (heightCopy root true))
  have left : (∑ e ∈ L', heightForestWeight G e) = ∑ e ∈ L, heightLinkWeight G root e := by
    rw [Finset.sum_map]
    rfl
  have right : (∑ e ∈ R', heightForestWeight G e) = ∑ e ∈ R, heightLinkWeight (reverseArcs G) root e := by
    rw [Finset.sum_map, reverseArcs, Finset.sum_image (fun _ _ _ _ eq => Prod.swap_injective eq)]
    apply sum_congr rfl
    intro e he
    have reversed := inwardHeightTree_edge_reach (hR he)
    have actual := reach_reverseArcs.mp reversed
    exact (hops_reverse_eq actual).symm
  calc
    _ ≤ (∑ e ∈ L' ∪ R', heightForestWeight G e) +
        ∑ e ∈ {heightForestRootLink root height}, heightForestWeight G e := sum_union_weight_le _ _ _
    _ = ∑ e ∈ L' ∪ R', heightForestWeight G e := by
      simp [heightForestRootLink, heightForestWeight]
    _ ≤ (∑ e ∈ L', heightForestWeight G e) + ∑ e ∈ R', heightForestWeight G e :=
      sum_union_weight_le _ _ _
    _ = _ := by rw [left, right]

/-- Expand selected metric forest links into original arcs. -/
def expandHeightForest (G : Arcs V) (links : Arcs (HeightForestVertex V height)) : Arcs V :=
  expandLabelledLinks G heightForestLabel links

theorem expandHeightForest_mono (G : Arcs V) :
    Monotone (expandHeightForest (height := height) G) :=
  expandLabelledLinks_mono G heightForestLabel

theorem expandHeightForest_sub (G : Arcs V) (links : Arcs (HeightForestVertex V height)) :
    expandHeightForest G links ⊆ G :=
  expandLabelledLinks_sub G heightForestLabel links

theorem expandHeightForest_cost (G : Arcs V) (links : Arcs (HeightForestVertex V height)) :
    (expandHeightForest G links).card ≤ ∑ e ∈ links, heightForestWeight G e :=
  expandLabelledLinks_cost G heightForestLabel links

theorem expandHeightForest_serves {G : Arcs V} {links : Arcs (HeightForestVertex V height)}
    (sub : links ⊆ heightForest G height) {d : V × V} (good : heightForestServes links d) :
    Reach (expandHeightForest G links) d.1 d.2 := by
  obtain ⟨a, b, source, sink, route⟩ := good
  have reach := expandLabelledLinks_reach (G := G) (label := heightForestLabel)
    (fun _ e => (heightForest_edge_spec (sub e)).2) route
  rwa [source.2.2, sink.2.2] at reach

private theorem embedJunctionPiece {G Z : Arcs V} (sub : Z ⊆ G) (piece : JunctionPiece Z)
    (P : Finset (V × V)) (pPos : 0 < P.card) {height : ℕ} (heightPos : 0 < height) :
    ∃ links : Arcs (HeightForestVertex V height), links ⊆ heightForest G height ∧
      (∀ d ∈ P, d ∈ piece.demands → heightForestServes links d) ∧
      (∑ e ∈ links, (heightForestWeight G e : ℝ)) ≤
        (4 * (height : ℝ) * (P.card : ℝ) ^ (1 / (height : ℝ))) * (piece.cost : ℝ) := by
  let D := piece.demands ∩ P
  let sources := D.image Prod.fst
  let sinks := D.image Prod.snd
  have sReach : ∀ v ∈ sources, Reach piece.inward v piece.root := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hv
    exact (piece.served d (mem_inter.mp hd).1).1
  have tReach : ∀ v ∈ sinks, Reach (reverseArcs piece.outward) v piece.root := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hv
    exact reach_reverseArcs.mpr (piece.served d (mem_inter.mp hd).1).2
  have sourceCount : sources.card ≤ P.card := card_image_le.trans (card_le_card inter_subset_right)
  have sinkCount : sinks.card ≤ P.card := card_image_le.trans (card_le_card inter_subset_right)
  obtain ⟨L, lSub, lService, lCost⟩ := rootedHeightEmbedding_bounded G piece.inward piece.root
    (piece.inward_sub.trans sub) piece.inward_tree sources sReach heightPos pPos sourceCount
  obtain ⟨R, rSub, rService, rCost⟩ := rootedHeightEmbedding_bounded (reverseArcs G)
    (reverseArcs piece.outward) piece.root (reverseArcs_mono (piece.outward_sub.trans sub))
    piece.outward_tree sinks tReach heightPos pPos sinkCount
  refine ⟨joinHeightCopies piece.root L R, joinHeightCopies_sub lSub rSub, ?_, ?_⟩
  · intro d hp hd
    have present : d ∈ D := mem_inter.mpr ⟨hd, hp⟩
    obtain ⟨sl, depthL, labelL, first⟩ := lService d.1 (mem_image_of_mem _ present)
    obtain ⟨tl, depthR, labelR, last⟩ := rService d.2 (mem_image_of_mem _ present)
    exact ⟨heightCopy piece.root false sl, heightCopy piece.root true tl,
      ⟨rfl, depthL, labelL⟩, ⟨rfl, depthR, labelR⟩, joinHeightCopies_route first last⟩
  · let factor := 4 * (height : ℝ) * (P.card : ℝ) ^ (1 / (height : ℝ))
    have changeCost : (∑ e ∈ joinHeightCopies piece.root L R, (heightForestWeight G e : ℝ)) ≤
        (∑ e ∈ L, (heightLinkWeight G piece.root e : ℝ)) +
          ∑ e ∈ R, (heightLinkWeight (reverseArcs G) piece.root e : ℝ) := by
      exact_mod_cast joinHeightCopies_weight_le rSub (L := L)
    simp only [reverseArcs_card] at rCost
    change _ ≤ factor * (piece.cost : ℝ)
    calc
      _ ≤ _ := changeCost
      _ ≤ factor * (piece.inward.card : ℝ) + factor * (piece.outward.card : ℝ) := add_le_add lCost rCost
      _ = _ := by simp [JunctionPiece.cost, mul_add]

/-- The weighted fixed forest comparator for a set of original demands,
with both template sides joined at each root. -/
theorem heightForest_comparison (G Z : Arcs V) (sub : Z ⊆ G) (P : Finset (V × V))
    (pPos : 0 < P.card) (reachable : ∀ d ∈ P, Reach Z d.1 d.2)
    {height : ℕ} (heightPos : 0 < height) :
    ∃ links : Arcs (HeightForestVertex V height), links ⊆ heightForest G height ∧
      (∀ d ∈ P, heightForestServes links d) ∧
      (∑ e ∈ links, (heightForestWeight G e : ℝ)) ≤
        12 * (height : ℝ) * (P.card : ℝ) ^ (1 / (height : ℝ)) *
          ((Nat.sqrt P.card : ℝ) + 1) * (Z.card : ℝ) := by
  classical
  obtain ⟨pieces, cover, _, pieceCost⟩ := junctionCover_sqrt_distinct Z P reachable
  let linksFor (i : Fin pieces.length) :=
    Classical.choose (embedJunctionPiece sub (pieces.get i) P pPos heightPos)
  have properties (i : Fin pieces.length) := Classical.choose_spec
    (embedJunctionPiece sub (pieces.get i) P pPos heightPos)
  let links := (univ : Finset (Fin pieces.length)).biUnion linksFor
  refine ⟨links, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact (properties i).1 hi
  · intro d hd
    obtain ⟨piece, found, hit⟩ := cover d hd
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp found
    obtain ⟨a, b, src, dst, route⟩ := (properties i).2.1 d hd hit
    exact ⟨a, b, src, dst, reach_mono (fun e he => mem_biUnion.mpr ⟨i, mem_univ _, he⟩) route⟩
  · let factor := 4 * (height : ℝ) * (P.card : ℝ) ^ (1 / (height : ℝ))
    have sumBound : (∑ e ∈ links, (heightForestWeight G e : ℝ)) ≤
        ∑ i : Fin pieces.length, ∑ e ∈ linksFor i, (heightForestWeight G e : ℝ) := by
      exact_mod_cast (sum_biUnion_weight_le (univ : Finset (Fin pieces.length)) linksFor (heightForestWeight G))
    have charged : (∑ i : Fin pieces.length, ((pieces.get i).cost : ℝ)) ≤
        3 * ((Nat.sqrt P.card : ℝ) + 1) * (Z.card : ℝ) := by
      rw [← Nat.cast_sum, ← list_weight_sum_get _ _]
      exact_mod_cast pieceCost
    calc
      _ ≤ _ := sumBound
      _ ≤ ∑ i : Fin pieces.length, factor * ((pieces.get i).cost : ℝ) :=
        sum_le_sum fun i _ => (properties i).2.2
      _ = factor * ∑ i : Fin pieces.length, ((pieces.get i).cost : ℝ) := (mul_sum ..).symm
      _ ≤ factor * (3 * ((Nat.sqrt P.card : ℝ) + 1) * (Z.card : ℝ)) :=
        mul_le_mul_of_nonneg_left charged (by dsimp [factor]; positivity)
      _ = _ := by dsimp [factor]; ring

end OnlineReachabilityPreservers
