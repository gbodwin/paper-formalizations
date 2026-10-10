import LightSpanners.BucketPaths
import LightSpanners.CycleProjection
import LightSpanners.TourCycle
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace LightSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}

omit [DecidableEq V] in
/-- A simple cycle supported on a nonnegative-weight walk cannot weigh more
than that walk, even when the walk repeats edges. -/
theorem cycle_weight_le_walk {u v r : V} (p : G.Walk u v) (q : G.Walk r r)
    (hq : q.IsCycle) (he : q.edges ⊆ p.edges) (hw : ∀ e ∈ p.edges, 0 ≤ w e) :
    walkWeight w q ≤ walkWeight w p := by
  obtain ⟨l, hl, hs⟩ := hq.isTrail.edges_nodup.subperm he
  have hsum := sublist_weight_le_on w hs hw
  simpa only [walkWeight, (hl.map w).sum_eq] using hsum

omit [DecidableEq V] in
/-- Non-backtracking in an acyclic support graph forces an actual simple path. -/
theorem isPath_of_no_supported_cycle {u v : V} (p : G.Walk u v)
    (hnb : p.edges.IsChain (· ≠ ·))
    (hno : ∀ r (q : G.Walk r r), q.IsCycle → ¬ q.edges ⊆ p.edges) : p.IsPath := by
  let H := p.toSubgraph.spanningCoe
  have hHG : H ≤ G := p.toSubgraph.spanningCoe_le
  have hH : H.IsAcyclic := by
    intro r q hq
    apply hno r (q.mapLe hHG) (hq.mapLe hHG)
    intro e he
    have hh := q.edges_subset_edgeSet (by simpa only [Walk.edges_mapLe_eq_edges] using he)
    simpa only [H, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph] using hh
  have hpH : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    simpa only [H, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph] using he
  have hp := (hH.isPath_iff_isChain (p.transfer H hpH)).mpr (by simpa using hnb)
  exact (Walk.isPath_transfer hpH).mp hp

namespace UnitSpanningCycle
variable (C : UnitSpanningCycle G w)

/-- Passing to undirected edges after filtering cycle darts agrees with
filtering the walk's edge list directly. -/
theorem cycleDarts_map_edges {u v : V} (p : G.Walk u v) :
    (C.cycleDarts p).map Dart.edge = p.edges.filter (fun e => e ∈ C.cycle.edges) := by
  induction p with
  | nil => rfl
  | @cons u v z h p ih =>
    by_cases he : s(u,v) ∈ C.cycle.edges <;>
      simp [cycleDarts, Walk.darts_cons, Walk.edges_cons, he] at ih ⊢ <;> exact ih

variable [Fintype V]

/-- Any simple cycle using only the spanning-cycle edges has n edges. -/
theorem base_cycle_length {r : V} (q : G.Walk r r) (hq : q.IsCycle)
    (he : ∀ e ∈ q.edges, e ∈ C.cycle.edges) : q.length = Fintype.card V := by
  let H := C.cycle.toSubgraph.spanningCoe
  have hH : H.Connected := by
    let : Nonempty V := ⟨C.base⟩
    refine ⟨fun u v => ?_⟩
    obtain ⟨p, hp, _⟩ := C.exists_short_arc u v
    refine ⟨p.transfer H ?_⟩
    intro e he
    simpa only [H, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph] using hp e he
  have hqH : ∀ e ∈ q.edges, e ∈ H.edgeSet := by
    intro e he'
    simpa only [H, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph] using he e he'
  have hham := cycle_hamiltonian_of_connected_isCycles hH
    C.hamiltonian.isCycle.isCycles_spanningCoe_toSubgraph
    (q.transfer H hqH) (hq.transfer hqH)
  simpa using hham.length_eq

/-- A supported base-only cycle requires at least n cycle steps in the walk. -/
theorem base_cycle_length_le_cycleDarts {u v r : V} (p : G.Walk u v)
    (q : G.Walk r r) (hq : q.IsCycle) (he : q.edges ⊆ p.edges)
    (hbase : ∀ e ∈ q.edges, e ∈ C.cycle.edges) :
    Fintype.card V ≤ (C.cycleDarts p).length := by
  have hs : q.edges ⊆ p.edges.filter (fun e => e ∈ C.cycle.edges) := by
    intro e heq
    simpa using (show e ∈ p.edges ∧ e ∈ C.cycle.edges from ⟨he heq, hbase e heq⟩)
  have hlen := (hq.isTrail.edges_nodup.subperm hs).length_le
  rw [← C.cycleDarts_map_edges p, List.length_map, Walk.length_edges,
    C.base_cycle_length q hq hbase] at hlen
  exact hlen

/-- A nonempty safe bucket walk with at most k chords is simple under the
paper's weighted-girth threshold. This is the within-bucket part of Claim 3. -/
theorem BucketSafe.isPath_of_chord {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    (h : C.BucketSafe eps k i p) (heps : 0 < eps) (hk : 0 < k)
    (hcount : (C.chordEdges p).length ≤ k)
    (hchord : (C.chordEdges p) ≠ [])
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) : p.IsPath := by
  have hpos : (0 : ℝ) < 2^i := by positivity
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hkr1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod : (0 : ℝ) < eps*k*2^i := by positivity
  have hg : (0 : ℝ) ≤ (1+4*eps)*(2*k) := by positivity
  have hbudget := BucketSafe.cycle_budget C h
  have hweight := BucketSafe.weight_budget C h
  obtain ⟨s, hb, _⟩ := h
  have hcountR : ((C.chordEdges p).length : ℝ) ≤ k := by exact_mod_cast hcount
  have hweight' : walkWeight w p ≤ (2+2*eps)*k*2^i := by
    have ht := mul_le_mul_of_nonneg_right hcountR (by positivity : (0 : ℝ) ≤ 2^(i+1))
    rw [pow_succ] at hweight ht
    nlinarith
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hchord
  have hed : e ∈ p.edges ∧ e ∉ C.cycle.edges := by simpa [chordEdges] using he
  have hi := (hb.2.1 e he).1
  have hwmax : w e < (Fintype.card V : ℝ) / (2*((1+4*eps)*(2*k)-1)) := by
    induction e using Sym2.inductionOn with
    | hf a b =>
      exact C.chord_weight_lt hG (by nlinarith [mul_pos heps hkr])
        ((mem_edgeSet G).mp (p.edges_subset_edgeSet hed.1)) hed.2
  have hden : 0 < 2*((1+4*eps)*(2*k)-1) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hsteps : ((C.cycleDarts p).length : ℝ) < Fintype.card V := by
    have hc := (lt_div_iff₀ hden).mp hwmax
    have ht := mul_le_mul_of_nonneg_right hi hden.le
    have hkp := mul_le_mul_of_nonneg_right hkr1 hpos.le
    nlinarith
  apply isPath_of_no_supported_cycle p hb.1
  intro r q hq hqp
  by_cases hbq : ∀ e ∈ q.edges, e ∈ C.cycle.edges
  · have hc := C.base_cycle_length_le_cycleDarts p q hq hqp hbq
    have hcR : (Fintype.card V : ℝ) ≤ (C.cycleDarts p).length := by exact_mod_cast hc
    linarith
  · push Not at hbq
    obtain ⟨d, hd, hdn⟩ := hbq
    have hdp : d ∈ C.chordEdges p := by simp [chordEdges, hqp hd, hdn]
    have hdw := (hb.2.1 d hdp).1
    have hcycle := hG r q hq d hd
    have hle := cycle_weight_le_walk p q hq hqp
      (fun e he => zero_le_one.trans (C.lower e (p.edges_subset_edgeSet he)))
    have hscale := mul_le_mul_of_nonneg_left hdw hg
    nlinarith


/-- Every safe bucket block with at most k chords has no repeated chord.
The empty-chord case is explicit and needs no bucket-weight witness. -/
theorem BucketSafe.chordEdges_nodup {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    (h : C.BucketSafe eps k i p) (heps : 0 < eps) (hk : 0 < k)
    (hcount : (C.chordEdges p).length ≤ k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) : (C.chordEdges p).Nodup := by
  by_cases he : C.chordEdges p = []
  · simp [he]
  · exact (h.isPath_of_chord C heps hk hcount he hG).isTrail.edges_nodup.filter _

omit [Fintype V] in
theorem bucket_safe_of_mode {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    {extra : Bool} (h : if extra then C.BucketExtraSafe eps k i p else C.BucketSafe eps k i p) :
    C.BucketSafe eps k i p := by
  cases extra with
  | false => exact h
  | true => exact BucketExtraSafe.safe C h

omit [Fintype V] in
/-- Every chord in a prefix of j buckets has weight strictly below 2^j. -/
theorem BucketMonotoneWalk.chord_weight_lt {eps : ℝ} {k j : ℕ} {extra : Bool}
    {u v : V} {p : G.Walk u v} (h : C.BucketMonotoneWalk eps k extra j p) :
    ∀ e ∈ C.chordEdges p, w e < 2^j := by
  induction h with
  | nil u => simp
  | @snoc j u v z p q hp hq ih =>
    intro e he
    rw [C.chordEdges_append, List.mem_append] at he
    rcases he with he | he
    · have hb := ih e he
      have hx : (0 : ℝ) < 2^j := by positivity
      rw [pow_succ]
      linarith
    · obtain ⟨_, hq, _⟩ := bucket_safe_of_mode C hq
      exact (hq.2.1 e he).2

/-- Claim 3 for actual concatenated bucket walks. Each block is simple when
nonempty in chords; disjoint dyadic intervals prevent cross-block repeats. -/
theorem BucketMonotoneWalk.chordEdges_nodup {eps : ℝ} {k j : ℕ} {extra : Bool}
    {u v : V} {p : G.Walk u v} (h : C.BucketMonotoneWalk eps k extra j p)
    (heps : 0 < eps) (hk : 0 < k)
    (hcount : (C.chordEdges p).length ≤ k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) : (C.chordEdges p).Nodup := by
  induction h with
  | nil u => simp
  | @snoc j u v z p q hp hq ih =>
    have hsafe := bucket_safe_of_mode C hq
    rw [C.chordEdges_append, List.length_append] at hcount
    have hpc : (C.chordEdges p).length ≤ k := by omega
    have hqc : (C.chordEdges q).length ≤ k := by omega
    rw [C.chordEdges_append, List.nodup_append]
    refine ⟨ih hpc, hsafe.chordEdges_nodup C heps hk hqc hG, ?_⟩
    intro e hep d hd heq
    subst d
    have hpw := hp.chord_weight_lt C e hep
    obtain ⟨_, hqb, _⟩ := hsafe
    have hqw := (hqb.2.1 e hd).1
    linarith

theorem BucketMonotoneKPath.chordEdges_nodup {eps : ℝ} {k : ℕ} {extra : Bool}
    {u v : V} {p : G.Walk u v} (h : C.BucketMonotoneKPath eps k extra p)
    (heps : 0 < eps) (hk : 0 < k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) : (C.chordEdges p).Nodup := by
  obtain ⟨hlen, j, hj⟩ := h
  exact hj.chordEdges_nodup C heps hk hlen.le hG

end UnitSpanningCycle
end LightSpanners
