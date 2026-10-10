import LightEFTSpanners.Blocking
import LightEFTSpanners.TreePruning

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Delete a first edge whenever any of its blocking partners survived sampling. -/
noncomputable def cleanGraph (X : SimpleGraph V) (B : Sym2 V → Finset (Sym2 V)) :
    SimpleGraph V := edgeGraph (X.edgeFinset.filter (fun e => Disjoint (B e) X.edgeFinset))

@[simp] theorem mem_cleanGraph (X : SimpleGraph V) (B : Sym2 V → Finset (Sym2 V))
    (e : Sym2 V) :
    e ∈ (cleanGraph X B).edgeSet ↔ e ∈ X.edgeSet ∧ Disjoint (B e) X.edgeFinset := by
  rw [cleanGraph,mem_edgeGraph]
  constructor
  · rintro ⟨h,_⟩
    exact ⟨mem_edgeFinset.mp (mem_filter.mp h).1,(mem_filter.mp h).2⟩
  · rintro ⟨hx,hd⟩
    have he := mem_edgeFinset.mpr hx
    exact ⟨mem_filter.mpr ⟨he,hd⟩,X.not_isDiag_of_mem_edgeFinset he⟩

theorem cleanGraph_le (X : SimpleGraph V) (B : Sym2 V → Finset (Sym2 V)) :
    cleanGraph X B ≤ X := by
  intro u v h
  exact (mem_edgeSet X).mp ((mem_cleanGraph X B _).mp ((mem_edgeSet _).mpr h)).1

theorem cleanGraph_no_blocking_pair (X : SimpleGraph V) (B : Sym2 V → Finset (Sym2 V))
    {e d : Sym2 V} (he : e ∈ (cleanGraph X B).edgeSet)
    (hd : d ∈ (cleanGraph X B).edgeSet) : d ∉ B e := by
  intro hB
  exact disjoint_left.mp ((mem_cleanGraph X B e).mp he).2 hB
    (mem_edgeFinset.mpr ((mem_cleanGraph X B d).mp hd).1)

theorem seedTree_le_cleanGraph {G T X : SimpleGraph V} {seed : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w t f B) (hTX : T ≤ X)
    (hTseed : ∀ e ∈ T.edgeSet, e ∈ seed) :
    T ≤ cleanGraph X B := by
  intro u v huv
  have heT : s(u,v) ∈ T.edgeSet := (mem_edgeSet _).mpr huv
  apply (mem_edgeSet _).mp
  apply (mem_cleanGraph X B _).mpr
  refine ⟨SimpleGraph.edgeSet_mono hTX heT,disjoint_left.mpr ?_⟩
  intro d hd _
  exact (hB.first_edge _ _ hd).2 (hTseed _ heT)

/-- The last deletion stage retains every chosen minimum-tree edge. -/
theorem tree_le_finalPrune {C T K : SimpleGraph V} (hKC : K ≤ C) :
    K ≤ C.deleteEdges (T.edgeSet \ K.edgeSet) := by
  intro u v huv
  apply deleteEdges_adj.mpr
  exact ⟨hKC huv,fun h => h.2 ((mem_edgeSet K).mpr huv)⟩

/-- Actual Lemma26 pruning on a host vertex set. Blocking deletion followed by
deleting seed-tree edges outside a bottleneck MST gives the required girth.
The spanning-tree and subset premises describe the host; no girth conclusion
or sampling oracle is assumed. -/
theorem finalPrune_girth {G T X K : SimpleGraph V} {seed : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w t f B) (hXG : X ≤ G)
    (hseed : ∀ e ∈ X.edgeSet, e ∈ seed → e ∈ T.edgeSet)
    (hK : K.IsTree) (hKC : K ≤ cleanGraph X B)
    (hbot : HasBottleneckPaths (cleanGraph X B) K w) (ht : 0 ≤ t+1) :
    WeightedGirthAbove ((cleanGraph X B).deleteEdges (T.edgeSet \ K.edgeSet)) w (t+1) := by
  let C := cleanGraph X B
  let R := C.deleteEdges (T.edgeSet \ K.edgeSet)
  have hRC : R ≤ C := SimpleGraph.deleteEdges_le (G := C) _
  have hRG : R ≤ G := hRC.trans ((cleanGraph_le X B).trans hXG)
  intro a p hp e hep
  by_contra hn
  have hweight : walkWeight w p ≤ (t+1)*w e := le_of_not_gt hn
  let pc := p.mapLe hRC
  obtain ⟨d,hd,hdK,hmax⟩ := cycle_maximum_outside_tree hK hKC hbot pc (hp.mapLe hRC)
  have hdp : d ∈ p.edges := by simpa [pc] using hd
  have hdX : d ∈ X.edgeSet :=
    SimpleGraph.edgeSet_mono (hRC.trans (cleanGraph_le X B)) (p.edges_subset_edgeSet hdp)
  have hdT : d ∉ T.edgeSet := by
    intro hdT
    have hh := p.edges_subset_edgeSet hdp
    rw [edgeSet_deleteEdges] at hh
    exact hh.2 ⟨hdT,hdK⟩
  have hdseed : d ∉ seed := fun hs => hdT (hseed d hdX hs)
  have hmaxep : w e ≤ w d := hmax e (by simpa [pc] using hep)
  have hwd : walkWeight w p ≤ (t+1)*w d :=
    hweight.trans (mul_le_mul_of_nonneg_left hmaxep ht)
  let pg := p.mapLe hRG
  obtain ⟨x,hx,y,hy,hyB⟩ := hB.blocks a pg (hp.mapLe hRG) d
    (by simpa [pg] using hdp) hdseed (by simpa [pg] using hwd)
  have hxC : x ∈ C.edgeSet := SimpleGraph.edgeSet_mono hRC
    (p.edges_subset_edgeSet (by simpa [pg] using hx))
  have hyC : y ∈ C.edgeSet := SimpleGraph.edgeSet_mono hRC
    (p.edges_subset_edgeSet (by simpa [pg] using hy))
  exact cleanGraph_no_blocking_pair X B hxC hyC hyB

/-- The needed tree is constructed by Kruskal, and remains an actual MST after
the final deletion. Its weight is bounded by the original host tree weight. -/
theorem exists_finalPrune {G T X : SimpleGraph V} {seed : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w t f B) (hXG : X ≤ G) (hT : T.IsTree)
    (hTX : T ≤ X) (hTseed : ∀ e ∈ T.edgeSet, e ∈ seed)
    (hseed : ∀ e ∈ X.edgeSet, e ∈ seed → e ∈ T.edgeSet) (ht : 0 ≤ t+1) :
    ∃ K : SimpleGraph V, let R := (cleanGraph X B).deleteEdges (T.edgeSet \ K.edgeSet)
      IsMinimumSpanningTree R K w ∧
      totalWeight K w ≤ totalWeight T w ∧ WeightedGirthAbove R w (t+1) := by
  have hTC := seedTree_le_cleanGraph hB hTX hTseed
  obtain ⟨K,hKC,hK,hbot⟩ := exists_bottleneck_spanning_tree (cleanGraph X B) w
    (hT.connected.mono hTC)
  have hmin := minimumSpanningTree_of_bottleneck hK hKC hbot
  refine ⟨K,⟨tree_le_finalPrune hKC,hK,?_⟩,hmin.2.2 T hTC hT,
    finalPrune_girth hB hXG hseed hK hKC hbot ht⟩
  intro S hSR hS
  exact hmin.2.2 S (hSR.trans (SimpleGraph.deleteEdges_le (G := cleanGraph X B) _)) hS
end LightEFTSpanners
