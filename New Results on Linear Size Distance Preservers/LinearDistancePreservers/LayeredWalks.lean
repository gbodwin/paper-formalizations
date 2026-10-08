import LinearDistancePreservers.WalkSequence
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Native unweighted walks in a layered graph. A shortest route from the
first layer to the last uses one vertex per layer; any backward step makes
it strictly longer. This is the metric step in the unweighted Lemma 7. -/
namespace LinearDistancePreservers.LayeredWalks
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def Layered (G : SimpleGraph V) (layer : V → ℤ) : Prop :=
  ∀ u v, G.Adj u v → layer v - layer u = 1 ∨ layer v - layer u = -1

theorem layer_le_length (layer : V → ℤ) (hG : Layered G layer)
    {s t : V} (p : G.Walk s t) : layer t - layer s ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp [SimpleGraph.Walk.length_nil]
  | cons h p ih =>
    have := hG _ _ h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    rcases this with h | h <;> omega

/-- Equality in the layer lower bound rules out every backward dart. -/
theorem tight_walk_rises (layer : V → ℤ) (hG : Layered G layer)
    {s t : V} (p : G.Walk s t) (htight : layer t - layer s = (p.length : ℤ)) :
    ∀ d ∈ p.darts, layer d.snd = layer d.fst + 1 := by
  induction p with
  | nil => simp
  | @cons s u t h p ih =>
    have htail := layer_le_length layer hG p
    have hs := hG s u h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] at htight
    have hsu : layer u - layer s = 1 := by omega
    have htt : layer t - layer u = (p.length : ℤ) := by omega
    intro d hd
    simp only [SimpleGraph.Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · change layer u = layer s + 1
      omega
    · exact ih htt d hd

/-- Once uniqueness is proved for rising routes, it is uniqueness among
all shortest walks in the actual undirected graph. -/
theorem unique_shortest_of_rising (layer : V → ℤ) (hG : Layered G layer)
    {s t : V} (p : G.Walk s t) (htight : layer t - layer s = (p.length : ℤ))
    (hunique : ∀ q : G.Walk s t,
      (∀ d ∈ q.darts, layer d.snd = layer d.fst + 1) → q = p) :
    ∀ q : G.Walk s t, q.length ≤ p.length → q = p := by
  intro q hq
  have hlo := layer_le_length layer hG q
  have heq : layer t - layer s = (q.length : ℤ) := by omega
  exact hunique q (tight_walk_rises layer hG q heq)

end LinearDistancePreservers.LayeredWalks
