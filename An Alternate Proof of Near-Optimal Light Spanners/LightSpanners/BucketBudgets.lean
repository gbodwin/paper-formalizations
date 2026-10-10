import LightSpanners.BucketUniqueness
import LightSpanners.Girth

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Actual cycle-step budget for a prefix of j buckets, indexed from zero. -/
theorem BucketMonotoneWalk.cycle_budget {eps : ℝ} {k j : ℕ} {extra : Bool}
    {u v : V} {p : G.Walk u v} (h : C.BucketMonotoneWalk eps k extra j p) :
    ((C.cycleDarts p).length : ℝ) ≤ 2*eps*k*((2:ℝ)^j-1) := by
  induction h with
  | nil u => simp
  | @snoc j u v z p q hp hq ih =>
    have hq' := (bucket_safe_of_mode C hq).cycle_budget C
    rw [C.cycleDarts_append,List.length_append,Nat.cast_add,pow_succ]
    nlinarith

/-- Count the distinct chords in a supported cycle against the actual two
walks; overlap between the walks only makes the upper bound weaker. -/
theorem cycle_chords_le_union {u v z : V} (p q : G.Walk u v) (c : G.Walk z z)
    (hc : c.IsCycle) (hs : ∀ e ∈ c.edges, e ∈ p.edges ∨ e ∈ q.edges) :
    (C.chordEdges c).length ≤ (C.chordEdges p).length + (C.chordEdges q).length := by
  have hn : (C.chordEdges c).Nodup := hc.isTrail.edges_nodup.filter _
  have hsub : C.chordEdges c ⊆ C.chordEdges p ++ C.chordEdges q := by
    intro e he
    have hh : e ∈ c.edges ∧ e ∉ C.cycle.edges := by simpa [chordEdges] using he
    rcases hs e hh.1 with hp | hq
    · simp [chordEdges,hp,hh.2]
    · simp [chordEdges,hq,hh.2]
  simpa only [List.length_append] using (hn.subperm hsub).length_le

/-- The same support count for unit cycle steps, preserving multiplicity
in the ambient walks while using simplicity of the extracted cycle. -/
theorem cycle_steps_le_union {u v z : V} (p q : G.Walk u v) (c : G.Walk z z)
    (hc : c.IsCycle) (hs : ∀ e ∈ c.edges, e ∈ p.edges ∨ e ∈ q.edges) :
    (C.cycleDarts c).length ≤ (C.cycleDarts p).length + (C.cycleDarts q).length := by
  have hn : ((C.cycleDarts c).map Dart.edge).Nodup := by
    rw [C.cycleDarts_map_edges]
    exact hc.isTrail.edges_nodup.filter _
  have hsub : (C.cycleDarts c).map Dart.edge ⊆
      (C.cycleDarts p).map Dart.edge ++ (C.cycleDarts q).map Dart.edge := by
    rw [C.cycleDarts_map_edges,C.cycleDarts_map_edges,C.cycleDarts_map_edges]
    intro e he
    have hh : e ∈ c.edges ∧ e ∈ C.cycle.edges := by simpa using he
    rcases hs e hh.1 with hp | hq
    · simp [hp,hh.2]
    · simp [hq,hh.2]
  simpa only [List.length_append,List.length_map] using (hn.subperm hsub).length_le


/-- The graph-level weight contradiction after a top-bucket cycle is
extracted from two actual prefixes. All counting budgets are derived. -/
theorem no_top_bucket_cycle {eps : ℝ} {k j : ℕ} {extra : Bool} {u v z : V}
    (p q : G.Walk u v) (c : G.Walk z z)
    (hp : C.BucketMonotoneWalk eps k extra (j+1) p)
    (hq : C.BucketMonotoneWalk eps k extra (j+1) q)
    (hpc : (C.chordEdges p).length ≤ k) (hqc : (C.chordEdges q).length ≤ k)
    (heps : 0 < eps) (hk : 0 < k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k)))
    (hc : c.IsCycle) (hs : ∀ e ∈ c.edges, e ∈ p.edges ∨ e ∈ q.edges)
    (htop : ∃ e ∈ c.edges, (2:ℝ)^j ≤ w e) : False := by
  obtain ⟨m,hm,hmax⟩ := exists_max_cycle_edge w c hc
  obtain ⟨e,he,heW⟩ := htop
  have hW : (2:ℝ)^j ≤ w m := heW.trans (hmax e he)
  have hW0 : 0 < w m := (by positivity : (0:ℝ) < 2^j).trans_le hW
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hcount := C.cycle_chords_le_union p q c hc hs
  have hcountR : ((C.chordEdges c).length : ℝ) ≤ 2*k := by exact_mod_cast (show (C.chordEdges c).length ≤ 2*k by omega)
  have hbase := C.cycle_steps_le_union p q c hc hs
  have hbaseR : ((C.cycleDarts c).length : ℝ) ≤
      (C.cycleDarts p).length + (C.cycleDarts q).length := by exact_mod_cast hbase
  have hpb := hp.cycle_budget C
  have hqb := hq.cycle_budget C
  rw [pow_succ] at hpb hqb
  have hsteps : ((C.cycleDarts c).length : ℝ) < 8*eps*k*2^j := by
    nlinarith [mul_pos heps hkR]
  have hstepsW := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 8*eps*k)
  have hweight := C.walkWeight_le_chord_bound c (w m) (fun f hf =>
    hmax f (List.mem_filter.mp hf).1)
  have hcountW := mul_le_mul_of_nonneg_right hcountR hW0.le
  have hg := hG z c hc m hm
  nlinarith

end LightSpanners.UnitSpanningCycle
