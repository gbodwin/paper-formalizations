import LightEFTSpanners.SeededGreedy

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [DecidableEq V]

/-- Functional representation of the ordered blocking pairs of Definition 19.
Only non-seed first edges can have blockers; every blocker is an actual graph
edge, no edge blocks itself, and each first edge has at most f blockers. -/
structure BlockingData (G : SimpleGraph V) (seed : Finset (Sym2 V))
    (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) (B : Sym2 V → Finset (Sym2 V)) : Prop where
  capped : ∀ e, (B e).card ≤ f
  second_edge : ∀ e d, d ∈ B e → d ∈ G.edgeSet
  first_edge : ∀ e d, d ∈ B e → e ∈ G.edgeSet ∧ e ∉ seed
  no_self : ∀ e, e ∉ B e
  blocks : ∀ a (p : G.Walk a a), p.IsCycle → ∀ d ∈ p.edges, d ∉ seed →
    walkWeight w p ≤ (t+1)*w d → ∃ e ∈ p.edges, ∃ d ∈ p.edges, d ∈ B e

/-- A rejected fault-coverage test supplies a bounded actual old-edge fault set. -/
theorem not_ftCovered_witness (E : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f : ℕ) (e : Sym2 V) (hc : ¬ FTCovered (edgeGraph E) w t f e) :
    ∃ F : Finset (Sym2 V), F ⊆ E ∧ F.card ≤ f ∧ e ∉ F ∧
      ¬ Covered (afterFaults (edgeGraph E) F) w t e := by
  rw [test_restrict_faults] at hc
  push Not at hc
  exact hc

/-- The new edge and one of its witness faults block every sufficiently light
cycle passing through the new edge. Old seed edges may have arbitrary weights. -/
theorem inserted_cycle_blocked (E : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (e : Sym2 V) (F : Finset (Sym2 V))
    (hc : ¬ Covered (afterFaults (edgeGraph E) F) w t e)
    {a : V} (p : (edgeGraph (insert e E)).Walk a a) (hp : p.IsCycle)
    (he : e ∈ p.edges) (hweight : walkWeight w p ≤ (t+1)*w e) :
    ∃ d ∈ p.edges, d ∈ F := by
  classical
  by_contra! hn
  obtain ⟨u,v,heq,q,hqw,hqe⟩ := cycle_complement p hp w he
  have hqold : ∀ d ∈ q.edges, d ∈ (afterFaults (edgeGraph E) F).edgeSet := by
    intro d hd
    obtain ⟨hdp,hdne⟩ := hqe d hd
    obtain ⟨hdi,hnd⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hdp)
    exact (mem_afterFaults _ _ _).mpr
      ⟨(mem_edgeGraph _ _).mpr ⟨(mem_insert.mp hdi).resolve_left hdne,hnd⟩,hn d hdp⟩
  have hbad := not_covered_witness hc v u (Sym2.eq_swap.trans heq.symm)
    (q.transfer (afterFaults (edgeGraph E) F) hqold)
  simp only [walkWeight_transfer] at hbad
  nlinarith

/-- Lemma 20 for the actual seeded recursion, with weight ties resolved by the
recursion order. No generic packing or blocking oracle is assumed. -/
theorem greedy_has_blocking (seed : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (t : ℝ) (f : ℕ) (ht : 0 ≤ t+1) (l : List (Sym2 V))
    (hs : l.Pairwise (fun e d => w d ≤ w e)) (hn : l.Nodup)
    (hdis : ∀ e ∈ l, e ∉ seed) (hdiag : ∀ e ∈ seed ∪ l.toFinset, ¬ e.IsDiag) :
    ∃ B : Sym2 V → Finset (Sym2 V),
      BlockingData (edgeGraph (greedyEdges seed w t f l)) seed w t f B := by
  classical
  induction l with
  | nil =>
    refine ⟨fun _ => ∅, ?_⟩
    constructor
    · intro e; simp
    · intro e d hd; simp at hd
    · intro e d hd; simp at hd
    · intro e; simp
    · intro a p hp d hd hdn hw
      have hh := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hd)
      exact (hdn hh.1).elim
  | cons e es ih =>
    obtain ⟨hmax,hs⟩ := List.pairwise_cons.mp hs
    obtain ⟨hene,hn⟩ := List.nodup_cons.mp hn
    have hdis' : ∀ d ∈ es, d ∉ seed := fun d hd => hdis d (by simp [hd])
    have hdiag' : ∀ d ∈ seed ∪ es.toFinset, ¬ d.IsDiag := by
      intro d hd
      apply hdiag d
      simpa using Or.inr hd
    obtain ⟨B,hB⟩ := ih hs hn hdis' hdiag'
    let E := greedyEdges seed w t f es
    have heE : e ∉ E := by
      intro he
      have hh := greedy_subset seed w t f es he
      rcases mem_union.mp hh with hh | hh
      · exact hdis e (by simp) hh
      · exact hene (List.mem_toFinset.mp hh)
    simp only [greedyEdges]
    split_ifs with hc
    · exact ⟨B,hB⟩
    · obtain ⟨F,hFE,hFc,heF,hbad⟩ := not_ftCovered_witness E w t f e hc
      let B' : Sym2 V → Finset (Sym2 V) := fun d => if d=e then F else B d
      refine ⟨B',?_⟩
      constructor
      · intro d
        by_cases hd : d=e
        · simpa [B',hd] using hFc
        · simpa [B',hd] using hB.capped d
      · intro d x hx
        by_cases hd : d=e
        · have hxF : x∈F := by simpa [B',hd] using hx
          exact (mem_edgeGraph _ _).mpr ⟨mem_insert_of_mem (hFE hxF),
            hdiag' x (greedy_subset seed w t f es (hFE hxF))⟩
        · have hxB : x∈B d := by simpa [B',hd] using hx
          exact SimpleGraph.edgeSet_mono (edgeGraph_mono (subset_insert e E)) (hB.second_edge d x hxB)
      · intro d x hx
        by_cases hd : d=e
        · subst d
          exact ⟨(mem_edgeGraph _ _).mpr ⟨mem_insert_self _ _,hdiag e (by simp)⟩,
            hdis e (by simp)⟩
        · have hxB : x∈B d := by simpa [B',hd] using hx
          obtain ⟨hed,hds⟩ := hB.first_edge d x hxB
          exact ⟨SimpleGraph.edgeSet_mono (edgeGraph_mono (subset_insert e E)) hed,hds⟩
      · intro d
        by_cases hd : d=e
        · simpa [B',hd] using heF
        · simpa [B',hd] using hB.no_self d
      · intro a p hp d hd hdn hw
        by_cases hep : e∈p.edges
        · have hdle : w d ≤ w e := by
            obtain ⟨hdi,_⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hd)
            rcases mem_insert.mp hdi with rfl | hdi
            · exact le_rfl
            · have hh := greedy_subset seed w t f es hdi
              exact hmax d (List.mem_toFinset.mp ((mem_union.mp hh).resolve_left hdn))
          have hwe : walkWeight w p ≤ (t+1)*w e := hw.trans (mul_le_mul_of_nonneg_left hdle ht)
          obtain ⟨x,hxp,hxF⟩ := inserted_cycle_blocked E w t e F hbad p hp hep hwe
          exact ⟨e,hep,x,hxp,by simpa [B'] using hxF⟩
        · have hold : ∀ x∈p.edges, x∈(edgeGraph E).edgeSet := by
            intro x hx
            obtain ⟨hxi,hnd⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hx)
            exact (mem_edgeGraph _ _).mpr
              ⟨(mem_insert.mp hxi).resolve_left (fun he => hep (he ▸ hx)),hnd⟩
          have hde : d ∈ (p.transfer (edgeGraph E) hold).edges := by
            rw [Walk.edges_transfer]; exact hd
          have hwp : walkWeight w (p.transfer (edgeGraph E) hold) ≤ (t+1)*w d := by
            rw [walkWeight_transfer]; exact hw
          obtain ⟨x,hxp,y,hyp,hyB⟩ := hB.blocks a (p.transfer (edgeGraph E) hold)
            (hp.transfer hold) d hde hdn hwp
          rw [Walk.edges_transfer] at hxp hyp
          have hxne : x ≠ e := fun he => hep (he ▸ hxp)
          exact ⟨x,hxp,y,hyp,by simpa [B',hxne] using hyB⟩

variable [Fintype V]
attribute [local instance] Classical.propDecidable

theorem input_sorted (G Q : SimpleGraph V) (w : Sym2 V → ℝ) :
    (input G Q w).Pairwise (fun e d => w d ≤ w e) :=
  List.Pairwise.filter _ (LightSpanners.greedyInput_sorted G w)

theorem input_nodup (G Q : SimpleGraph V) (w : Sym2 V → ℝ) :
    (input G Q w).Nodup := by
  have h : (LightSpanners.greedyInput G w).Nodup :=
    (LightSpanners.greedyInput_perm G w).nodup_iff.mpr (nodup_toList _)
  exact h.filter _

/-- Full finite-graph Lemma 20 wrapper for Algorithm 1. The stronger cycle
condition implies the source statement whenever a heaviest cycle edge is
outside the seed, with no distinct-edge-weight assumption. -/
theorem output_has_blocking (G Q : SimpleGraph V) (hQ : Q ≤ G)
    (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) (ht : 0 ≤ t+1) :
    ∃ B : Sym2 V → Finset (Sym2 V),
      BlockingData (output G Q w t f) Q.edgeFinset w t f B := by
  apply greedy_has_blocking Q.edgeFinset w t f ht (input G Q w)
    (input_sorted G Q w) (input_nodup G Q w)
  · intro e he
    exact ((mem_input G Q w e).mp he).2
  · intro e he
    rcases mem_union.mp he with he | he
    · exact Q.not_isDiag_of_mem_edgeFinset he
    · exact G.not_isDiag_of_mem_edgeFinset ((mem_input G Q w e).mp (List.mem_toFinset.mp he)).1

end LightEFTSpanners
