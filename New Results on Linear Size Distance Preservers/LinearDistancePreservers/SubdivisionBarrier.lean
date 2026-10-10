import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

namespace LinearDistancePreservers.SubdivisionBarrier
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A bounded-degree vertex cover bounds the entire actual graph, even if
vertices outside the cover have arbitrarily large degree. -/
theorem edges_le_degree_cover (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (hcover : ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S)
    (hdegree : ∀ v ∈ S, G.degree v ≤ k) : G.edgeFinset.card ≤ k*S.card := by
  classical
  have hsub : G.edgeFinset ⊆ S.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := by simpa using he
      rcases hcover u v hadj with hu | hv
      · exact mem_biUnion.mpr ⟨u,hu,by simp [hadj]⟩
      · exact mem_biUnion.mpr ⟨v,hv,by simp [SimpleGraph.mk'_mem_incidenceSet_iff,hadj]⟩
  calc
    G.edgeFinset.card ≤ (S.biUnion (fun v => G.incidenceFinset v)).card := card_le_card hsub
    _ ≤ ∑ v ∈ S, (G.incidenceFinset v).card := card_biUnion_le
    _ = ∑ v ∈ S, G.degree v := by simp
    _ ≤ ∑ _v ∈ S, k := sum_le_sum hdegree
    _ = k*S.card := by simp [mul_comm]

/-- In every full private subdivision, old vertices are independent and all
new vertices have degree two. This abstract graph criterion alone implies
linear density; it does not assume any special preserver construction. -/
theorem edges_le_twice_new_vertices (G : SimpleGraph V) (old : Finset V)
    (hold : ∀ u ∈ old, ∀ v ∈ old, ¬G.Adj u v)
    (hnew : ∀ v ∉ old, G.degree v ≤ 2) :
    G.edgeFinset.card ≤ 2*(Fintype.card V-old.card) := by
  have h := edges_le_degree_cover G (univ\old) 2 (by
    intro u v hadj
    by_cases hu : u ∈ old
    · right
      have hv : v ∉ old := fun hv => hold u hu v hv hadj
      simpa using hv
    · left
      simpa using hu) (by intro v hv; exact hnew v (mem_sdiff.mp hv).2)
  simpa [card_sdiff_of_subset (subset_univ old)] using h

/-- The whole graph is an actual native-distance preserver for every terminal
set, so this graph family admits a linear-size preserver for every demand. -/
theorem exists_linear_native_preserver (G : SimpleGraph V) (old terminals : Finset V)
    (hold : ∀ u ∈ old, ∀ v ∈ old, ¬G.Adj u v)
    (hnew : ∀ v ∉ old, G.degree v ≤ 2) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ s ∈ terminals, ∀ t ∈ terminals, H.edist s t = G.edist s t) ∧
      H.edgeFinset.card ≤ 2*Fintype.card V := by
  refine ⟨G,le_rfl,by simp,?_⟩
  exact (edges_le_twice_new_vertices G old hold hnew).trans (Nat.mul_le_mul_left 2 (Nat.sub_le _ _))

/-- Once the squared terminal count exceeds twice the vertex count, this
whole actual graph family already has a strictly subquadratic preserver. -/
theorem exists_preserver_lt_terminal_square (G : SimpleGraph V) (old terminals : Finset V)
    (hold : ∀ u ∈ old, ∀ v ∈ old, ¬G.Adj u v)
    (hnew : ∀ v ∉ old, G.degree v ≤ 2)
    (hsize : 2*Fintype.card V < terminals.card^2) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ s ∈ terminals, ∀ t ∈ terminals, H.edist s t = G.edist s t) ∧
      H.edgeFinset.card < terminals.card^2 := by
  obtain ⟨H,hsub,hpres,hcard⟩ := exists_linear_native_preserver G old terminals hold hnew
  exact ⟨H,hsub,hpres,hcard.trans_lt hsize⟩

end LinearDistancePreservers.SubdivisionBarrier
