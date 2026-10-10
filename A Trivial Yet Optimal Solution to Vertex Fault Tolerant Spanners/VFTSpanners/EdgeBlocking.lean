import VFTSpanners.EdgeMain
import VFTSpanners.EdgeLimitation

/-!
# Edge-blocking witness for the EFT greedy algorithm

The unnumbered edge-fault analog of Lemma 3 in the concluding paragraph of
Bodwin–Patel, arXiv:1812.05778v2 (2019). The output is the actual weighted EFT
greedy graph. Every blocking pair consists of two distinct output edges.
-/

namespace VFTSpanners
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [DecidableEq V] in
/-- A rejected edge-fault coverage test gives an orientation-independent
fault witness that does not contain the queried edge. -/
theorem not_edgeCovered_witness {H : SimpleGraph V} {w : Sym2 V → ℝ} {k f : ℕ}
    {e : Sym2 V} (h : ¬ EdgeCovered H w k f e) :
    ∃ F : Finset (Sym2 V), F.card ≤ f ∧ e ∉ F ∧
      ∀ u v, s(u,v) = e → ∀ p : H.Walk u v,
        EdgeAvoids F p → (k : ℝ)*w e < walkWeight w p := by
  classical
  simp only [EdgeCovered] at h
  push Not at h
  obtain ⟨u,v,he,F,hF,heF,hbad⟩ := h
  refine ⟨F,hF,heF,?_⟩
  intro a b hab p hp
  rcases Sym2.eq_iff.mp (hab.trans he.symm) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hbad p hp
  · have hrev : EdgeAvoids F p.reverse := by simpa [EdgeAvoids] using hp
    simpa [walkWeight] using hbad p.reverse hrev

/-- When the EFT greedy algorithm adds an edge, its fault witness extends
an edge-blocking set by at most `f` pairs. Failed labels outside the old
 graph are filtered out, so all pairs are genuine edges of the output. -/
theorem extend_edgeBlocking (E : Finset (Sym2 V))
    (B : Finset (Sym2 V × Sym2 V)) (w : Sym2 V → ℝ) (k f : ℕ) (e : Sym2 V)
    (he : ¬ e.IsDiag) (hne : e ∉ E) (hw : 0 ≤ w e)
    (hmax : ∀ d ∈ E, w d ≤ w e)
    (hB : IsEdgeBlockingSet (edgeGraph E) (k+1) (B : Set _))
    (hb : B.card ≤ f*E.card) (hc : ¬ EdgeCovered (edgeGraph E) w k f e) :
    ∃ C : Finset (Sym2 V × Sym2 V),
      IsEdgeBlockingSet (edgeGraph (insert e E)) (k+1) (C : Set _) ∧
      C.card ≤ f*(insert e E).card := by
  classical
  obtain ⟨F,hF,heF,hbad⟩ := not_edgeCovered_witness hc
  let D := F.filter fun d => d ∈ (edgeGraph E).edgeSet
  let C := B ∪ D ×ˢ {e}
  have hmono : edgeGraph E ≤ edgeGraph (insert e E) := edgeGraph_mono (subset_insert _ _)
  refine ⟨C,⟨?_,?_⟩,?_⟩
  · intro d d' hdd'
    rcases mem_union.mp hdd' with hdd' | hdd'
    · obtain ⟨hd,hd',hne⟩ := hB.1 hdd'
      exact ⟨edgeSet_mono hmono hd, edgeSet_mono hmono hd', hne⟩
    · obtain ⟨hd,hd'⟩ := mem_product.mp hdd'
      have hd'e : d' = e := mem_singleton.mp hd'
      subst d'
      obtain ⟨hdF,hdE⟩ := mem_filter.mp hd
      exact ⟨edgeSet_mono hmono hdE,
        (mem_edgeGraph _ _).mpr ⟨mem_insert_self _ _,he⟩,
        fun h => heF (h ▸ hdF)⟩
  · intro a p hp hlen
    by_cases hep : e ∈ p.edges
    · obtain ⟨u,v,huv,q,hqlen,hqe,_⟩ := cycle_complement p hp hep
      have hqold : ∀ d ∈ q.edges, d ∈ (edgeGraph E).edgeSet := by
        intro d hd
        obtain ⟨hdp,hdne⟩ := hqe d hd
        obtain ⟨hdi,hndi⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hdp)
        exact (mem_edgeGraph _ _).mpr ⟨(mem_insert.mp hdi).resolve_left hdne,hndi⟩
      let q' := q.transfer (edgeGraph E) hqold
      have hcost : walkWeight w q' ≤ (k : ℝ)*w e := by
        have hl : q.length ≤ k := by omega
        have hl' : (q.length : ℝ) ≤ k := by exact_mod_cast hl
        have hqw := walkWeight_le w q (w e) (fun d hd =>
          hmax d ((mem_edgeGraph _ _).mp (hqold d hd)).1)
        simp only [q', walkWeight_transfer]
        exact hqw.trans (mul_le_mul_of_nonneg_right hl' hw)
      have hinter : ∃ d ∈ q.edges, d ∈ F := by
        by_contra hn
        push Not at hn
        have hav : EdgeAvoids F q' := by simpa [EdgeAvoids,q'] using hn
        have heq : s(v,u) = e := Sym2.eq_swap.trans huv.symm
        exact (not_lt_of_ge hcost) (hbad v u heq q' hav)
      obtain ⟨d,hd,hdF⟩ := hinter
      have hdD : d ∈ D := mem_filter.mpr ⟨hdF,hqold d hd⟩
      exact ⟨d,e,mem_union_right _ (mem_product.mpr ⟨hdD,mem_singleton_self _⟩),
        (hqe d hd).1,hep⟩
    · have hold : ∀ d ∈ p.edges, d ∈ (edgeGraph E).edgeSet := by
        intro d hd
        obtain ⟨hdi,hndi⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hd)
        have hde : d ≠ e := fun h => hep (h ▸ hd)
        exact (mem_edgeGraph _ _).mpr ⟨(mem_insert.mp hdi).resolve_left hde,hndi⟩
      have hcycle : (p.transfer (edgeGraph E) hold).IsCycle := hp.transfer hold
      obtain ⟨d,d',hdd',hd,hd'⟩ :=
        hB.2 (p.transfer (edgeGraph E) hold) hcycle (by simpa using hlen)
      exact ⟨d,d',mem_union_left _ hdd',by simpa using hd,by simpa using hd'⟩
  · have hcard := card_union_le B (D ×ˢ {e})
    have hD : D.card ≤ F.card := card_filter_le _ _
    simp only [card_product, card_singleton, mul_one] at hcard
    rw [card_insert_of_notMem hne]
    change (B ∪ D ×ˢ {e}).card ≤ _
    nlinarith

/-- The EFT analog of Lemma 3 for any nondecreasing-weight edge order. -/
theorem edgeGreedy_edgeBlocking (w : Sym2 V → ℝ) (k f : ℕ)
    (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V))
    (hnd : l.Nodup) (hs : l.Pairwise (fun e d => w d ≤ w e))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    ∃ B : Finset (Sym2 V × Sym2 V),
      IsEdgeBlockingSet (edgeGraph (edgeGreedyEdges w k f l)) (k+1) (B : Set _) ∧
      B.card ≤ f*(edgeGreedyEdges w k f l).card := by
  classical
  induction l with
  | nil =>
    refine ⟨∅,⟨by simp,?_⟩,by simp [edgeGreedyEdges]⟩
    intro a p hp
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | cons h p => simp [edgeGreedyEdges,edgeGraph] at h
  | cons e es ih =>
    obtain ⟨hne,hnd⟩ := List.nodup_cons.mp hnd
    obtain ⟨hmax,hs⟩ := List.pairwise_cons.mp hs
    obtain ⟨B,hB,hcard⟩ := ih hnd hs (fun d hd => hl d (by simp [hd]))
    simp only [edgeGreedyEdges]
    split_ifs with hc
    · exact ⟨B,hB,hcard⟩
    · apply extend_edgeBlocking _ B w k f e (hl e (by simp)) _ (hw e) _ hB hcard hc
      · exact fun he => hne (List.mem_toFinset.mp (edgeGreedyEdges_subset w k f es he))
      · intro d hd
        exact hmax d (List.mem_toFinset.mp (edgeGreedyEdges_subset w k f es hd))

/-- Every actual weighted EFT greedy output has an edge `(k+1)`-blocking set
of cardinality at most `f` times its number of edges. -/
theorem edgeGreedyOutput_edgeBlocking [Fintype V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (k f : ℕ) (hw : ∀ e, 0 ≤ w e) :
    ∃ B : Finset (Sym2 V × Sym2 V),
      IsEdgeBlockingSet (edgeGreedyOutput G w k f) (k+1) (B : Set _) ∧
      B.card ≤ f*(edgeGreedyOutput G w k f).edgeFinset.card := by
  rw [edgeGreedyOutput_edgeFinset]
  exact edgeGreedy_edgeBlocking w k f hw (greedyInput G w)
    ((greedyInput_perm G w).nodup_iff.mpr G.edgeFinset.nodup_toList)
    (greedyInput_sorted G w)
    (fun e he => G.not_isDiag_of_mem_edgeFinset ((mem_greedyInput G w e).mp he))

end VFTSpanners
