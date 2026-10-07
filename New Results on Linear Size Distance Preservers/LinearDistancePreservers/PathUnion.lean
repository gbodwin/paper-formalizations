import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-! Actual directed weighted walks and distance preservation. Distances take
values in the extended nonnegative reals, so unreachable pairs have distance
infinity. No metric, triangle inequality, or distance-preserver conclusion
is assumed in the definitions. -/
namespace LinearDistancePreservers
open scoped ENNReal

namespace WeightedDigraph
variable {V I : Type*}

def IsWalk (G : V → V → Prop) (s t : V) (p : List V) : Prop :=
  p.head? = some s ∧ p.getLast? = some t ∧
  ∀ e ∈ p.zip p.tail, G e.1 e.2

noncomputable def cost (w : V → V → ℝ≥0∞) (p : List V) : ℝ≥0∞ :=
  ((p.zip p.tail).map fun e => w e.1 e.2).sum

noncomputable def distance (G : V → V → Prop) (w : V → V → ℝ≥0∞)
    (s t : V) : ℝ≥0∞ :=
  sInf {c | ∃ p, IsWalk G s t p ∧ c = cost w p}

theorem distance_le_cost {G : V → V → Prop} {w : V → V → ℝ≥0∞}
    {s t : V} {p : List V} (h : IsWalk G s t p) : distance G w s t ≤ cost w p :=
  sInf_le ⟨p,h,rfl⟩

theorem distance_mono {G H : V → V → Prop} (w : V → V → ℝ≥0∞)
    (hsub : ∀ u v, H u v → G u v) (s t : V) : distance G w s t ≤ distance H w s t := by
  apply sInf_le_sInf
  rintro c ⟨p,hp,rfl⟩
  exact ⟨p,⟨hp.1,hp.2.1,fun e he => hsub _ _ (hp.2.2 e he)⟩,rfl⟩

def PathUnion (paths : I → List V) (u v : V) : Prop :=
  ∃ i, (u,v) ∈ (paths i).zip (paths i).tail

theorem path_union_subgraph {G : V → V → Prop} (paths : I → List V)
    (s t : I → V) (hvalid : ∀ i, IsWalk G (s i) (t i) (paths i)) :
    ∀ u v, PathUnion paths u v → G u v := by
  rintro u v ⟨i,hi⟩
  exact (hvalid i).2.2 (u,v) hi

/-- Unioning selected shortest paths gives equality of the actual distances. -/
theorem path_union_preserves {G : V → V → Prop} (w : V → V → ℝ≥0∞)
    (paths : I → List V) (s t : I → V)
    (hvalid : ∀ i, IsWalk G (s i) (t i) (paths i))
    (hshortest : ∀ i, cost w (paths i) = distance G w (s i) (t i)) (i : I) :
    distance (PathUnion paths) w (s i) (t i) = distance G w (s i) (t i) := by
  apply le_antisymm
  · rw [← hshortest i]
    apply distance_le_cost
    exact ⟨(hvalid i).1,(hvalid i).2.1,fun e he => ⟨i,he⟩⟩
  · exact distance_mono w (path_union_subgraph paths s t hvalid) _ _

/-- A unique shortest path forces each of its edges into any subgraph with
an attained, equal shortest distance. This is the forcing step of Section 4. -/
theorem unique_shortest_forces_edges {G H : V → V → Prop} (w : V → V → ℝ≥0∞)
    (s t : V) (p q : List V)
    (hsub : ∀ u v, H u v → G u v)
    (hunique : ∀ r, IsWalk G s t r → cost w r = distance G w s t → r = p)
    (hq : IsWalk H s t q) (hshort : cost w q = distance H w s t)
    (hpres : distance H w s t = distance G w s t) :
    ∀ e ∈ p.zip p.tail, H e.1 e.2 := by
  have hqG : IsWalk G s t q :=
    ⟨hq.1,hq.2.1,fun e he => hsub _ _ (hq.2.2 e he)⟩
  have heq : q = p := hunique q hqG (hshort.trans hpres)
  simpa [heq] using hq.2.2

end WeightedDigraph
end LinearDistancePreservers
