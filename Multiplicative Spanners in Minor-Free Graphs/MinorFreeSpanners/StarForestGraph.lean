import MinorFreeSpanners.FullStarEdgeAccounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Package the actual selected center-leaf edges as a real acyclic spanning
subgraph. The selected vertex set remains explicit; residual vertices are
isolated in this forest, and are retained later by the full contraction. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

/-- The genuine simple graph consisting precisely of selected star edges. -/
def starForestGraph (C : Finset V) (L : V → Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ b ∈ C, (x=b ∧ y ∈ L b) ∨ (y=b ∧ x ∈ L b)
  symm := ⟨by
    rintro x y ⟨hne,b,hb,h⟩
    exact ⟨hne.symm,b,hb,h.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [DecidableEq V] in
/-- Every forest edge is an actual original-host edge. -/
theorem IsStarPacking.starForest_le {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L) :
    starForestGraph C L ≤ G := by
  rintro x y ⟨_,b,_,he⟩
  rcases he with ⟨hxb,hy⟩|⟨hyb,hx⟩
  · rw [hxb]
    exact h.2.2.1 b y hy
  · rw [hyb]
    exact (h.2.2.1 b x hx).symm

/-- A selected leaf has only its unique actual center as a forest neighbor. -/
theorem IsStarPacking.starForest_leaf_neighbor {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) {b x y : V} (hx : x ∈ L b)
    (he : (starForestGraph C L).Adj x y) : y=b := by
  obtain ⟨_,c,hc,he⟩ := he
  rcases he with ⟨hxc,_⟩|⟨hyc,hx'⟩
  · exact (Finset.disjoint_left.mp hAC (h.2.1 b hx) (hxc.symm ▸ hc)).elim
  · have hcb : c=b := by
      by_contra hn
      exact Finset.disjoint_left.mp (h.2.2.2.2.1 c b hn) hx' hx
    exact hyc.trans hcb

/-- A cycle cannot pass through a selected leaf: its predecessor and
successor would both be that leaf's unique center. -/
theorem IsStarPacking.starForest_no_cycle_at_leaf {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) {b x : V} (hx : x ∈ L b)
    (p : (starForestGraph C L).Walk x x) : ¬ p.IsCycle := by
  intro hp
  have hs := h.starForest_leaf_neighbor hAC hx (p.adj_snd hp.not_nil)
  have ht := h.starForest_leaf_neighbor hAC hx (p.adj_penultimate hp.not_nil).symm
  exact hp.snd_ne_penultimate (hs.trans ht.symm)

/-- Every cycle would have a leaf endpoint on its first edge; rotating to
that real vertex rules it out. Thus the graph is literally a forest. -/
theorem IsStarPacking.starForest_acyclic {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) : (starForestGraph C L).IsAcyclic := by
  intro x p hp
  obtain ⟨_,b,_,he⟩ := p.adj_snd hp.not_nil
  rcases he with ⟨_,hleaf⟩|⟨_,hleaf⟩
  · exact h.starForest_no_cycle_at_leaf hAC hleaf
      (p.rotate p.snd (List.mem_of_mem_tail (p.snd_mem_tail_support hp.not_nil)))
      (hp.rotate _)
  · exact h.starForest_no_cycle_at_leaf hAC hleaf p hp

/-- The actual forest-valued subgraph on precisely the covered vertices. -/
def IsStarPacking.starForestSubgraph {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L) : G.Subgraph where
  verts := (C.biUnion fun b => insert b (L b) : Finset V)
  Adj := (starForestGraph C L).Adj
  adj_sub := fun he => h.starForest_le he
  edge_vert := by
    rintro x y ⟨_,b,hb,he⟩
    apply Finset.mem_coe.mpr
    apply Finset.mem_biUnion.mpr
    refine ⟨b,hb,?_⟩
    rcases he with ⟨rfl,_⟩|⟨_,hx⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem hx
  symm := (starForestGraph C L).symm

/-- The packaged subgraph is genuinely acyclic. -/
theorem IsStarPacking.starForestSubgraph_acyclic {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) : h.starForestSubgraph.coe.IsAcyclic := by
  exact (h.starForest_acyclic hAC).comap
    ⟨Subtype.val, fun he => he⟩ Subtype.val_injective

/-- Every original left-side vertex has forest degree at most one, including
unselected vertices, which have no forest edges. -/
theorem IsStarPacking.starForest_left_degree_le_one [Fintype V]
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) (hAC : Disjoint A C) {x : V} (hx : x ∈ A) :
    (starForestGraph C L).degree x ≤ 1 := by
  classical
  rw [← (starForestGraph C L).card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro y hy z hz
  have hy' := (starForestGraph C L).mem_neighborFinset x y |>.mp hy
  have hz' := (starForestGraph C L).mem_neighborFinset x z |>.mp hz
  obtain ⟨_,b,hb,he⟩ := hy'
  rcases he with ⟨hxb,_⟩|⟨hyb,hxb⟩
  · exact (Finset.disjoint_left.mp hAC hx (hxb ▸ hb)).elim
  · exact hyb.trans (h.starForest_leaf_neighbor hAC hxb hz').symm

/-- The real forest graph has precisely the previously counted forest edges. -/
theorem IsStarPacking.starForest_edgeFinset [Fintype V]
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) :
    (starForestGraph C L).edgeFinset = starForestEdges C L := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
    rw [mem_edgeFinset]
    constructor
    · rintro ⟨_,b,hb,he⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨b,hb,?_⟩
      rcases he with ⟨hxb,hy⟩|⟨hyb,hx⟩
      · change x=b at hxb
        rw [hxb]
        exact Finset.mem_image.mpr ⟨y,hy,rfl⟩
      · change y=b at hyb
        rw [hyb]
        exact Finset.mem_image.mpr ⟨x,hx,Sym2.eq_swap⟩
    · intro he
      obtain ⟨b,hb,hbe⟩ := Finset.mem_biUnion.mp he
      obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hbe
      rcases Sym2.eq_iff.mp he with ⟨hbx,hzy⟩|⟨hby,hzx⟩
      · rw [← hbx,← hzy]
        exact ⟨(h.2.2.1 b z hz).ne,b,hb,Or.inl ⟨rfl,hz⟩⟩
      · rw [← hzx,← hby]
        exact ⟨(h.2.2.1 b z hz).ne.symm,b,hb,Or.inr ⟨rfl,hz⟩⟩

/-- Actual forest edges have the exact full-star edge count. -/
theorem IsStarPacking.starForest_edge_count [Fintype V]
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) (hAC : Disjoint A C)
    (hfull : ∀ b ∈ C, (L b).card=ell) :
    (starForestGraph C L).edgeFinset.card=ell*C.card := by
  rw [h.starForest_edgeFinset]
  exact h.starForest_card hAC hfull

end MinorFreeSpanners
