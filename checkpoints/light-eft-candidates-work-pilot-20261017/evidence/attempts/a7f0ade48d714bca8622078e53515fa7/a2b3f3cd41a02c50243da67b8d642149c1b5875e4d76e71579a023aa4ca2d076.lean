import LightSpanners.CycleOrder
import LightSpanners.BucketCycles

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Consecutive forward and backward steps necessarily backtrack. -/
theorem opposed_darts_same_edge {d e : G.Dart}
    (hd : d ∈ C.cycle.darts) (he : e.symm ∈ C.cycle.darts)
    (hadj : G.DartAdj d e) : d.edge = e.edge := by
  have hd' := (C.dart_mem_iff_successor d).mp hd
  have he' := (C.dart_mem_iff_successor e.symm).mp he
  have hfirst : d.fst = e.snd := C.successor.injective (hd'.trans (hadj.trans he'.symm))
  change s(d.fst,d.snd) = s(e.fst,e.snd)
  rw [hfirst,hadj]
  exact Sym2.eq_swap

theorem cycleDarts_eq_of_no_chords {u v : V} (p : G.Walk u v)
    (h : C.chordEdges p = []) : C.cycleDarts p = p.darts := by
  apply List.filter_eq_self.mpr
  intro d hd
  have he : d.edge ∈ p.edges := List.mem_map.mpr ⟨d,hd,rfl⟩
  by_contra hn
  have hn : d.edge ∉ C.cycle.edges := by simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using hn
  have hc : d.edge ∈ C.chordEdges p := by simp [chordEdges,he,hn]
  simp [h] at hc

/-- Empty-chord bucket blocks are genuinely empty walks. Equal forward and
backward budgets cannot hide a cycle-only excursion because the turnaround
would immediately backtrack. This includes the empty-block boundary case. -/
theorem BucketWalk.nil_of_no_chords {u v : V} {i s : ℕ} {p : G.Walk u v}
    (h : C.BucketWalk i s p) (hchord : C.chordEdges p = []) : p.Nil := by
  have hlen := C.length_split p
  rw [hchord, List.length_nil, zero_add, h.cycleDarts_length C] at hlen
  suffices hs : s = 0 by
    apply Walk.length_eq_zero_iff.mp
    omega
  by_contra hs
  obtain ⟨hnb, _, f,b,hfb,hf,hb,hforward,hbackward⟩ := h
  have hf0 : f ≠ [] := by intro he; simp [he] at hf; omega
  have hb0 : b ≠ [] := by intro he; simp [he] at hb; omega
  have hword : p.darts = f ++ b := (C.cycleDarts_eq_of_no_chords p hchord).symm.trans hfb
  have hchain := p.isChain_dartAdj_darts
  have hchainEdge : p.darts.IsChain (fun d e => d.edge ≠ e.edge) :=
    (List.isChain_map Dart.edge).mp hnb
  rw [hword] at hchain hchainEdge
  have hadj := hchain.rel_getLast_head_of_append hf0 hb0
  have hne := hchainEdge.rel_getLast_head_of_append hf0 hb0
  exact hne (C.opposed_darts_same_edge
    (hforward _ (List.getLast_mem hf0)) (hbackward _ (List.head_mem hb0)) hadj)

theorem BucketSafe.nil_of_no_chords {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    (h : C.BucketSafe eps k i p) (hchord : C.chordEdges p = []) : p.Nil := by
  obtain ⟨s,hs,_⟩ := h
  exact hs.nil_of_no_chords C hchord

variable [Fintype V]

/-- Two simple spanning-cycle arcs of combined length below n coincide.
The proof uses the actual base graph and extracts an actual cycle if they differ. -/
theorem short_base_paths_unique {u v : V} (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpe : ∀ e ∈ p.edges, e ∈ C.cycle.edges)
    (hqe : ∀ e ∈ q.edges, e ∈ C.cycle.edges)
    (hlen : p.length + q.length < Fintype.card V) : p = q := by
  let H := C.cycle.toSubgraph.spanningCoe
  have hHG : H ≤ G := C.cycle.toSubgraph.spanningCoe_le
  have hpH : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    simpa only [H, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph] using hpe e he
  have hqH : ∀ e ∈ q.edges, e ∈ H.edgeSet := by
    intro e he
    simpa only [H, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph] using hqe e he
  have heq : p.transfer H hpH = q.transfer H hqH := by
    by_contra hn
    obtain ⟨r,_,_,c,hc,hcsize⟩ := (hp.transfer hpH).exists_isCycle_length_le_add_of_ne
      (hq.transfer hqH) hn
    have hbase : ∀ e ∈ (c.mapLe hHG).edges, e ∈ C.cycle.edges := by
      intro e he
      have hh := c.edges_subset_edgeSet (by simpa only [Walk.edges_mapLe_eq_edges] using he)
      simpa only [H, Subgraph.edgeSet_spanningCoe, Walk.mem_edges_toSubgraph] using hh
    have hclen := C.base_cycle_length (c.mapLe hHG) (hc.mapLe hHG) hbase
    simp only [Walk.length_mapLe] at hclen
    simp only [Walk.length_transfer] at hcsize
    omega
  apply Walk.edges_injective
  simpa using congrArg Walk.edges heq

end LightSpanners.UnitSpanningCycle
