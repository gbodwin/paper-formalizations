import GreedyShortcuts.ChainTransitionCost

/-! Exact executable evaluation of the existing normalized distance, given
finite Boolean representations of the actual fixed-source filter and labels.
The representation equalities are explicit; filter construction is separate. -/
namespace GreedyShortcuts.ChainDistanceDP
open Finset SimpleGraph DirectedPaths ChainFirst ChainTransitionCost FiniteDistanceDP
open LinearDistancePreservers.ConsistentTiebreaking
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- One materialized n-horizon table, with the original unreachable-zero
convention applied only after the sentinel has been tested. -/
def evaluate (edge : Fin n → Fin n → Bool) (color : Fin n → Option I)
    (s t : Fin n) : ℕ :=
  let v := value edge (charge color) (n+1) t n s
  if v=n+1 then 0 else present (color s)+v

/-- The executable result is the literal existing minimum, including self,
uncovered, and originally unreachable pairs. No path-minimum oracle is input. -/
theorem evaluate_eq_distance (T : ChainDistance.Context (Fin n) I)
    (H : Finset (Fin n × Fin n)) (hH : H ⊆ candidates T.G)
    (edge : Fin n → Fin n → Bool) (color : Fin n → Option I) (s t : Fin n)
    (hEdge : ∀ u v,edge u v=true ↔ T.graph H s u v)
    (hColor : color=label T.chains) : evaluate edge color s t=T.distance H s t := by
  classical
  subst color
  by_cases hr : Reachable T.G s t
  · obtain ⟨p,hp,hpc⟩ := T.distance_spec H hr
    have hlen : p.length<n := by
      simpa only [Fintype.card_fin] using
        (ChainDistance.Context.allowed_isPath (T.graph_acyclic hH s) p hp).length_lt
    have hcost := count_eq_entry_cost T hH p hp
    have hbound := T.count_le_vertices p
    have hpB : Allowed (fun u v => edge u v=true) p := allowed_mono (fun u v h => (hEdge u v).mpr h) hp
    have hv := value_le_walk edge (charge (label T.chains)) (n+1) t n p hpB (by omega)
    have hlt : value edge (charge (label T.chains)) (n+1) t n s<n+1 := by omega
    obtain ⟨q,hq,_hlen,hqc⟩ := value_sound edge (charge (label T.chains)) (n+1) t n s hlt
    have hqT : Allowed (T.graph H s) q := allowed_mono (fun u v h => (hEdge u v).mp h) hq
    have hlow := T.distance_le_walk H hr q hqT
    have hqcost := count_eq_entry_cost T hH q hqT
    unfold evaluate
    rw [ite_eq_right (Nat.ne_of_lt hlt)]
    omega
  · have hcap : value edge (charge (label T.chains)) (n+1) t n s=n+1 := by
      apply Nat.le_antisymm (value_le_cap ..)
      by_contra hn
      have hlt : value edge (charge (label T.chains)) (n+1) t n s<n+1 := by omega
      obtain ⟨p,hp,_,_⟩ := value_sound edge (charge (label T.chains)) (n+1) t n s hlt
      have hpT : Allowed (augment T.G (T.base∪H)) p :=
        allowed_mono (fun u v h => ((hEdge u v).mp h).1) hp
      exact hr ((reachable_augment_iff T.G _ (T.augmentation_legal hH) s t).mp ⟨p,hpT⟩)
    simp [evaluate,hcap,ChainDistance.Context.distance,hr]

end GreedyShortcuts.ChainDistanceDP
