import MinorFreeSpanners.BoundedBranchMerge
import MinorFreeSpanners.MinorBranchDegree
import MinorFreeSpanners.SingletonNonmateChoice

/-! A proof-bearing actual star-growth state in a full simple contraction.
The selected branch contains the original center and only original neighbors;
all unused candidates remain literal singleton branches. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
universe u

structure CleanStarState {V : Type u} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (c : V) (T : Finset V) (q : ℝ) (initialVertices initialEdges r : ℕ) where
  Index : Type u
  finiteIndex : Fintype Index
  vertex_count : letI := finiteIndex
    Fintype.card Index+r=initialVertices+1
  graph : SimpleGraph Index
  model : MinorModel graph G
  covers : model.Covers
  full : model.IsFull
  bounded : model.IsBounded k
  center : Index
  center_mem : c ∈ model.branch center
  center_subset : model.branch center ⊆ (insert c T:Set V)
  center_card : (model.branch center).toFinset.card=r
  positive : 0 < r
  unused_singleton : ∀ x ∈ T, x ∉ model.branch center → ∃ i, model.branch i={x}
  edge_budget : letI := finiteIndex
    (initialEdges:ℝ) ≤ (graph.edgeFinset.card:ℝ) + 2*((r-1:ℕ):ℝ)*q

attribute [instance] CleanStarState.finiteIndex

end MinorFreeSpanners
