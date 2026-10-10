import LightSpanners.HikerCompletion

namespace LightSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : UnitSpanningCycle G w)

namespace WalkSquad

theorem morning_chord_mem (ds : List G.Dart) (v : V) (t : ℕ) :
    ∀ e ∈ C.chordEdges ((morning C ds t).path v), e ∈ ds.map Dart.edge := by
  induction t generalizing v with
  | zero =>
    intro e he
    exact (edgeLayer_edges_sublist ds v).subset (List.mem_filter.mp he).1
  | succ t ih =>
    change ∀ e ∈ C.chordEdges (((morning C ds t).path v).append
      ((Walk.cons (C.successor_adj _) .nil).append ((edgeLayer ds).path _))), _
    rw [C.chordEdges_append,C.chordEdges_append]
    have hm : s((morning C ds t).position v,C.successor ((morning C ds t).position v)) ∈ C.cycle.edges :=
      List.mem_map.mpr ⟨_,C.successor_dart _,rfl⟩
    simp only [UnitSpanningCycle.chordEdges,Walk.edges_cons,Walk.edges_nil,List.filter_cons,
      hm,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte,List.filter_nil,
      List.nil_append,List.mem_append]
    intro e he
    rcases he with he | he
    · exact ih v e he
    · exact (edgeLayer_edges_sublist ds _).subset (List.mem_filter.mp he).1

/-- A completed bucket day is an actual endpoint-permutation squad. The
backward completion preserves every chord and the exact total count. -/
theorem exists_bucket_day [Fintype V] (ds : List G.Dart) (i t : ℕ)
    (hds : (ds.map Dart.edge).Nodup)
    (hd : ∀ d ∈ ds, d.edge ∉ C.cycle.edges)
    (hw : ∀ d ∈ ds, (2:ℝ)^i ≤ w d.edge ∧ w d.edge < 2^(i+1))
    {eps : ℝ} {k : ℕ} (ht : (t:ℝ) ≤ eps*k*2^i/2) :
    ∃ A : WalkSquad G, (∀ v, C.BucketExtraSafe eps k i (A.path v)) ∧
      totalChords C A = 2*(t+1)*ds.length := by
  classical
  let M := morning C ds t
  let P : Equiv.Perm V := M.position.trans (C.successor.symm^t)
  have hq (v : V) : ∃ q : G.Walk v (P v),
      C.BucketExtraSafe eps k i q ∧ C.chordEdges q = C.chordEdges (M.path v) := by
    obtain ⟨s,q,hs,hbucket,hch⟩ := C.exists_balanced_completion (M.path v) i
      (morning_nonbacktracking C ds v hds hd t) (morning_cycle_forward C ds v hd t)
      (by intro e he
          obtain ⟨d,hd',rfl⟩ := List.mem_map.mp (morning_chord_mem C ds v t e he)
          exact hw d hd')
    have hcount : (C.cycleDarts (M.path v)).length = t := morning_cycle_count C ds v hd t
    have hend : (C.successor.symm : V → V)^[(C.cycleDarts (M.path v)).length] (M.position v) = P v := by
      simp [P,hcount,Equiv.Perm.coe_pow]
    refine ⟨q.copy rfl hend,?_,?_⟩
    · refine ⟨s,?_,?_⟩
      · exact C.bucketWalk_copy q rfl hend hbucket
      · exact (by exact_mod_cast (hs.trans_eq hcount) : (s:ℝ) ≤ t).trans ht
    · simpa [UnitSpanningCycle.chordEdges] using hch
  choose q hsafe hch using hq
  refine ⟨⟨P,q⟩,hsafe,?_⟩
  calc
    _ = totalChords C M := by unfold totalChords; simp only [hch]
    _ = _ := totalChords_morning C ds hd t

end WalkSquad
end LightSpanners
