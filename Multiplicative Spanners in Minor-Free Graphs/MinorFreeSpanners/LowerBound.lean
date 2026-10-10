import MinorFreeSpanners.Greedy

/-! The edge-forcing step of the lower-bound proof is unconditional.
The existence of asymptotically dense high-girth graphs is the paper's
explicit Erdős girth-conjecture premise and is not asserted here. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Any (2k−1)-spanner of an unweighted graph with girth >2k is the entire
graph. This proves the graph-level edge-forcing step of Theorems 7 and 13. -/
theorem high_girth_spanner_eq {G H : SimpleGraph V} (k : ℕ)
    (hG : GirthAbove G (2*k))
    (hspan : IsSpanner G H (fun _ => 1) (2*k-1)) : H = G := by
  apply le_antisymm hspan.1
  intro u v huv
  by_contra hH
  obtain ⟨q, hq⟩ := hspan.2 u v huv.toWalk
  have hwq := walkWeight_eq_length_mul q (fun _ => (1:ℝ)) 1 (by simp)
  simp only [SimpleGraph.Adj.toWalk, walkWeight_cons, walkWeight_nil, add_zero] at hq
  rw [hwq, mul_one, mul_one] at hq
  let p := q.bypass.mapLe hspan.1
  have hp : p.IsPath := q.bypass_isPath.mapLe hspan.1
  have he : s(v,u) ∉ p.edges := by
    intro he
    have hem : s(v,u) ∈ H.edgeSet := q.bypass.edges_subset_edgeSet (by simpa [p] using he)
    exact hH ((mem_edgeSet H).mp hem).symm
  have hc : (Walk.cons huv.symm p).IsCycle := (Walk.cons_isCycle_iff _ _).mpr ⟨hp,he⟩
  have hlong := hG v _ hc
  have hshort : q.bypass.length ≤ q.length := q.length_bypass_le_length
  have hlong' : 2*k < q.bypass.length+1 := by simpa [p] using hlong
  have hq' : (q.length:ℝ)+1 ≤ 2*k := by linarith
  have hq'' : q.length+1 ≤ 2*k := by exact_mod_cast hq'
  omega

end MinorFreeSpanners
