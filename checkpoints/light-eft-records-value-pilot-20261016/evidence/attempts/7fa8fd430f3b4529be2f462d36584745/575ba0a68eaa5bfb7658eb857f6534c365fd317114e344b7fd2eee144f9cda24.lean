import LightEFTSpanners.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

namespace LightEFTSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- The source's (f+1)-edge-connectivity conclusion in mathlib's native cut-set
semantics, obtained from the actual preserver definition. -/
theorem IsFTConnectivityPreserver.missing_edge_edgeReachable {G Q : SimpleGraph V}
    {f : ℕ} (h : IsFTConnectivityPreserver G Q f) {u v : V}
    (heG : G.Adj u v) (heQ : ¬ Q.Adj u v) : Q.IsEdgeReachable (f+1) u v := by
  intro s hs
  have hcard : s.toFinset.card ≤ f := by
    rw [Set.encard_eq_coe_toFinset_card] at hs
    exact Nat.le_of_lt_succ (by exact_mod_cast hs)
  simpa only [afterFaults, Set.coe_toFinset] using
    h.missing_edge_connected heG heQ s.toFinset hcard

/-- A missing edge forces at least f+1 surviving preserver edges incident to
its endpoint. This supplies a finite obstruction without a path-packing axiom. -/
theorem IsFTConnectivityPreserver.missing_edge_degree {G Q : SimpleGraph V}
    {f : ℕ} (h : IsFTConnectivityPreserver G Q f) {u v : V}
    (heG : G.Adj u v) (heQ : ¬ Q.Adj u v) : f+1 ≤ Q.degree u :=
  (h.missing_edge_edgeReachable heG heQ).le_degree heG.ne

/-- In maximum degree at most f+1, an f-fault connectivity preserver must keep
all edges. In particular every 1-fault finite-stretch spanner of a triangle
keeps all three edges, regardless of their positive weights or stretch. -/
theorem preserver_eq_of_degree_le {G Q : SimpleGraph V} {f : ℕ}
    (h : IsFTConnectivityPreserver G Q f) (hdeg : ∀ u, G.degree u ≤ f+1) : Q = G := by
  classical
  apply le_antisymm h.1
  intro u v huv
  by_contra hn
  have hQdeg := h.missing_edge_degree huv hn
  have hstrict : Q.neighborFinset u ⊂ G.neighborFinset u := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨?_,?_⟩
    · intro x hx
      exact (mem_neighborFinset G u x).mpr (h.1 ((mem_neighborFinset Q u x).mp hx))
    · intro heq
      have hv : v ∈ G.neighborFinset u := (mem_neighborFinset G u v).mpr huv
      rw [← heq] at hv
      exact hn ((mem_neighborFinset Q u v).mp hv)
  have hc := card_lt_card hstrict
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at hc
  have hh := hdeg u
  omega

end LightEFTSpanners
