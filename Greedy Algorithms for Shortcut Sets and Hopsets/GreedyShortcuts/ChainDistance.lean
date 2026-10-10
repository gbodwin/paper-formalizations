import GreedyShortcuts.ChainNormalization

/-! Actual source-dependent normalized distance for chain Algorithm 2.
The minimum is over real earliest-entry filtered walks. Its existence follows
from proved preprocessing, not from an assumed hereditary-optimality property. -/
namespace GreedyShortcuts.ChainDistance

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainUnion ChainFirst ChainNormalization
open NormalizedReachability
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

structure Context (V I : Type*) [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] where
  G : V → V → Prop
  acyclic : Acyclic G
  chains : I → Chain G
  disjoint : Pairwise (fun i j => Disjoint (chains i).support (chains j).support)
  K : ℕ
  witnesses : ∀ c,PathWitness (chains c).length K

namespace Context

variable (T : Context V I)

def base : Finset (V × V) := unionEdges T.chains T.witnesses

def graph (H : Finset (V × V)) (s : V) : V → V → Prop :=
  filtered (augment T.G (T.base ∪ H)) (label T.chains) (first T.chains) s

theorem graph_mono {H J : Finset (V × V)} (hHJ : H ⊆ J) (s u v : V) :
    T.graph H s u v → T.graph J s u v := by
  rintro ⟨huv,he⟩
  refine ⟨?_,he⟩
  rcases huv with hg | hh
  · exact Or.inl hg
  · exact Or.inr (Finset.mem_union.mp hh |>.elim
      (fun h => Finset.mem_union_left _ h) (fun h => Finset.mem_union_right _ (hHJ h)))

theorem reachable_graph (H : Finset (V × V)) {s t : V} (hr : Reachable T.G s t) :
    Reachable (T.graph H s) s t := by
  have hbase := (reachable_normalized_iff T.acyclic T.chains T.disjoint T.witnesses s t).mpr hr
  apply reachable_mono (H:=T.graph H s) ?_ hbase
  intro u v huv
  refine ⟨?_,huv.2⟩
  exact huv.1.elim Or.inl (fun he => Or.inr (Finset.mem_union_left H he))

noncomputable def chainSet {s t : V} (p : DWalk s t) : Finset I :=
  p.support.toFinset.biUnion (fun v => (label T.chains v).toFinset)

noncomputable def count {s t : V} (p : DWalk s t) : ℕ := (T.chainSet p).card

theorem count_le_chains {s t : V} (p : DWalk s t) : T.count p ≤ Fintype.card I :=
  Finset.card_le_univ _

theorem count_le_vertices {s t : V} (p : DWalk s t) : T.count p ≤ p.length+1 := by
  classical
  calc
    T.count p ≤ ∑ v ∈ p.support.toFinset,(label T.chains v).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ p.support.toFinset,1 := by
      apply Finset.sum_le_sum
      intro v hv
      cases label T.chains v <;> simp
    _ = p.support.toFinset.card := by simp
    _ ≤ p.support.length := List.toFinset_card_le _
    _ = p.length+1 := Walk.length_support p

theorem exists_cost (H : Finset (V × V)) {s t : V} (hr : Reachable T.G s t) :
    ∃ n : ℕ,∃ p : DWalk s t,Allowed (T.graph H s) p ∧ T.count p = n := by
  obtain ⟨p,hp⟩ := T.reachable_graph H hr
  exact ⟨T.count p,p,hp,rfl⟩

noncomputable def distance (H : Finset (V × V)) (s t : V) : ℕ := by
  classical
  exact if hr : Reachable T.G s t then Nat.find (T.exists_cost H hr) else 0

theorem distance_spec (H : Finset (V × V)) {s t : V} (hr : Reachable T.G s t) :
    ∃ p : DWalk s t,Allowed (T.graph H s) p ∧ T.count p = T.distance H s t := by
  classical
  simpa only [distance,dite_eq_left hr] using Nat.find_spec (T.exists_cost H hr)

theorem distance_le_walk (H : Finset (V × V)) {s t : V} (hr : Reachable T.G s t)
    (p : DWalk s t) (hp : Allowed (T.graph H s) p) : T.distance H s t ≤ T.count p := by
  classical
  simp only [distance,dite_eq_left hr]
  exact Nat.find_min' (T.exists_cost H hr) ⟨p,hp,rfl⟩

theorem distance_le_chains (H : Finset (V × V)) (s t : V) :
    T.distance H s t ≤ Fintype.card I := by
  classical
  by_cases hr : Reachable T.G s t
  · obtain ⟨p,hp,he⟩ := T.distance_spec H hr
    rw [← he]
    exact T.count_le_chains p
  · simp [distance,hr]

theorem distance_antitone (s t : V) : Antitone (fun H => T.distance H s t) := by
  classical
  intro H J hHJ
  by_cases hr : Reachable T.G s t
  · obtain ⟨p,hp,he⟩ := T.distance_spec H hr
    exact (T.distance_le_walk J hr p (allowed_mono (T.graph_mono hHJ s) hp)).trans_eq he
  · simp [distance,hr]

end Context
end GreedyShortcuts.ChainDistance
