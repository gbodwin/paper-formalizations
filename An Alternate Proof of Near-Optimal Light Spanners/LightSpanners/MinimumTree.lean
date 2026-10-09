import LightSpanners.Kruskal

namespace LightSpanners
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A walk crossing a reachability cut has an edge crossing that cut. -/
theorem exists_edge_not_reachable {G H : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (h : ¬ H.Reachable u v) :
    ∃ a b, G.Adj a b ∧ s(a,b) ∈ p.edges ∧ ¬ H.Reachable a b := by
  induction p with
  | nil => exact (h .rfl).elim
  | @cons u v z huv p ih =>
    by_cases huvH : H.Reachable u v
    · obtain ⟨a, b, hab, hmem, hn⟩ := ih (fun hvz => h (huvH.trans hvz))
      exact ⟨a, b, hab, by simp [hmem], hn⟩
    · exact ⟨u, v, huv, by simp, huvH⟩

variable [Fintype V]
attribute [local instance] Classical.propDecidable

noncomputable def totalWeight (G : SimpleGraph V) (w : Sym2 V → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, w e

def IsMinimumSpanningTree (G T : SimpleGraph V) (w : Sym2 V → ℝ) : Prop :=
  T ≤ G ∧ T.IsTree ∧ ∀ S : SimpleGraph V, S ≤ G → S.IsTree → totalWeight T w ≤ totalWeight S w

def HasBottleneckPaths (G T : SimpleGraph V) (w : Sym2 V → ℝ) : Prop :=
  ∀ u v, G.Adj u v → ∃ p : T.Walk u v, ∀ e ∈ p.edges, w e ≤ w s(u,v)

theorem exchange_edgeFinset (T : SimpleGraph V) {u v : V} (hne : u ≠ v)
    (f : Sym2 V) (i : Fintype ((T ⊔ SimpleGraph.edge u v).deleteEdges {f}).edgeSet) :
    @SimpleGraph.edgeFinset V ((T ⊔ SimpleGraph.edge u v).deleteEdges {f}) i =
      (insert s(u,v) T.edgeFinset).erase f := by
  ext e
  simp only [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, edgeSet_sup,
    Set.mem_union, edgeSet_edge_of_ne hne, Set.mem_singleton_iff, mem_erase, mem_insert]
  tauto

/-- An exchange decreases weight and strictly increases overlap with the target. -/
theorem tree_exchange {G K T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hK : K.IsTree) (hT : T.IsTree) (hKG : K ≤ G) (hTG : T ≤ G)
    (hopt : HasBottleneckPaths G K w) {u v : V}
    (heK : K.Adj u v) (heT : ¬ T.Adj u v) :
    ∃ T' : SimpleGraph V, T' ≤ G ∧ T'.IsTree ∧ totalWeight T' w ≤ totalWeight T w ∧
      (K.edgeFinset \ T'.edgeFinset).card < (K.edgeFinset \ T.edgeFinset).card := by
  classical
  let e := s(u,v)
  have heKmem : e ∈ K.edgeSet := (mem_edgeSet K).mpr heK
  have heTnot : e ∉ T.edgeSet := fun h => heT ((mem_edgeSet T).mp h)
  have hb : K.IsBridge e := isAcyclic_iff_forall_isBridge.mp hK.isAcyclic heKmem
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath v u
  have hcut : ¬ (K.deleteEdges {e}).Reachable v u := fun h => hb h.symm
  obtain ⟨a, b, hab, hfmem, hfcut⟩ := exists_edge_not_reachable p hcut
  let f := s(a,b)
  have hfT : f ∈ T.edgeSet := (mem_edgeSet T).mpr hab
  have hfe : f ≠ e := fun h => heTnot (h ▸ hfT)
  have hfK : f ∉ K.edgeSet := by
    intro h
    exact hfcut (Adj.reachable (deleteEdges_adj.mpr ⟨(mem_edgeSet K).mp h, hfe⟩))
  obtain ⟨q, hq⟩ := hopt a b (hTG hab)
  have heq : e ∈ q.edges := by
    by_contra hn
    apply hfcut
    refine ⟨q.transfer (K.deleteEdges {e}) ?_⟩
    intro d hd
    rw [edgeSet_deleteEdges]
    exact ⟨q.edges_subset_edgeSet hd, fun h => hn (h ▸ hd)⟩
  have hweight : w e ≤ w f := hq e heq
  let U := T ⊔ SimpleGraph.edge u v
  let T' := U.deleteEdges {f}
  have heU : U.Adj u v := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, heK.ne⟩)
  have hc : (Walk.cons heU (p.mapLe le_sup_left)).IsCycle := by
    apply (Walk.cons_isCycle_iff _ _).mpr
    refine ⟨hp.mapLe le_sup_left, ?_⟩
    intro h
    exact heTnot (p.edges_subset_edgeSet (by simpa using h))
  have hfcycle : f ∈ (Walk.cons heU (p.mapLe le_sup_left)).edges := by simp [hfmem, f]
  have hnotbridge : ¬ U.IsBridge f := fun h => h.notMem_edges_of_isCycle hc hfcycle
  have hconn : T'.Connected :=
    (hT.connected.mono le_sup_left).preconnected.connected_deleteEdges_of_not_isBridge hnotbridge
  have hfin : T'.edgeFinset = (insert e T.edgeFinset).erase f :=
    exchange_edgeFinset T heK.ne f _
  have hefin : e ∉ T.edgeFinset := by simpa using heTnot
  have hffin : f ∈ T.edgeFinset := by simpa using hfT
  have hcard : T'.edgeFinset.card = T.edgeFinset.card := by
    rw [hfin, card_erase_of_mem (mem_insert_of_mem hffin), card_insert_of_notMem hefin]
    omega
  have htree : T'.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card, hcard]
    simpa only [Nat.card_eq_fintype_card] using hT.card_edgeFinset
  refine ⟨T', (deleteEdges_le _).trans (sup_le hTG ?_), htree, ?_, ?_⟩
  · exact (edge_le_iff G).mpr (Or.inr (hKG heK))
  · unfold totalWeight
    dsimp only [T', U]
    rw [exchange_edgeFinset T heK.ne f _, sum_erase_eq_sub (mem_insert_of_mem hffin),
      sum_insert hefin]
    linarith
  · apply card_lt_card
    dsimp only [T', U]
    rw [exchange_edgeFinset T heK.ne f _]
    apply ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro d hd
      obtain ⟨hdK, hdT⟩ := mem_sdiff.mp hd
      refine mem_sdiff.mpr ⟨hdK, fun hdt => ?_⟩
      apply hdT
      exact mem_erase.mpr ⟨fun h => hfK (by simpa [h] using hdK), mem_insert_of_mem hdt⟩
    · intro hsets
      have heold : e ∈ K.edgeFinset \ T.edgeFinset := mem_sdiff.mpr
        ⟨by simpa using heKmem, hefin⟩
      rw [← hsets] at heold
      exact (mem_sdiff.mp heold).2 (mem_erase.mpr ⟨hfe.symm, mem_insert_self _ _⟩)

theorem minimumSpanningTree_of_bottleneck {G K : SimpleGraph V} {w : Sym2 V → ℝ}
    (hK : K.IsTree) (hKG : K ≤ G) (hopt : HasBottleneckPaths G K w) :
    IsMinimumSpanningTree G K w := by
  refine ⟨hKG, hK, ?_⟩
  intro T hTG hT
  generalize hn : (K.edgeFinset \ T.edgeFinset).card = n
  induction n using Nat.strong_induction_on generalizing T with
  | h n ih =>
    by_cases hKT : K ≤ T
    · have heq : K = T := le_antisymm hKT
        ((isTree_iff_minimal_connected.mp hT).2 hK.connected hKT)
      simp [heq]
    · have hex : ∃ u v, K.Adj u v ∧ ¬ T.Adj u v := by
        by_contra! hh
        exact hKT (fun u v huv => hh u v huv)
      obtain ⟨u, v, heK, heT⟩ := hex
      obtain ⟨T', hT'G, hT', hweight, hless⟩ := tree_exchange hK hT hKG hTG hopt heK heT
      exact (ih _ (hn ▸ hless) T' hT'G hT' rfl).trans hweight

theorem kruskal_isMinimumSpanningTree (w : Sym2 V → ℝ) (l : List (Sym2 V))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) (hs : l.Pairwise (fun a b => w b ≤ w a))
    (hconn : (edgeGraph l.toFinset).Connected) :
    IsMinimumSpanningTree (edgeGraph l.toFinset) (edgeGraph (kruskalEdges l)) w := by
  apply minimumSpanningTree_of_bottleneck (kruskal_isTree l hl hconn)
    (edgeGraph_mono (kruskalEdges_subset l))
  intro u v huv
  have he := (mem_edgeGraph _ _).mp ((mem_edgeSet _).mpr huv)
  obtain ⟨p, _, hp⟩ := kruskal_bottleneck w l hl hs s(u,v) (List.mem_toFinset.mp he.1) u v rfl
  exact ⟨p, hp⟩

theorem greedy_contains_mst (w : Sym2 V → ℝ) (t : ℝ) (l : List (Sym2 V))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) (hs : l.Pairwise (fun a b => w b ≤ w a))
    (hconn : (edgeGraph l.toFinset).Connected) :
    ∃ T : SimpleGraph V, T ≤ edgeGraph (greedyEdges w t l) ∧
      IsMinimumSpanningTree (edgeGraph l.toFinset) T w :=
  ⟨edgeGraph (kruskalEdges l), edgeGraph_mono (kruskal_subset_greedy w t l hl),
    kruskal_isMinimumSpanningTree w l hl hs hconn⟩

end LightSpanners
