import GreedyShortcuts.ChainDistanceDP

/-! A Boolean reachability computation from the supplied original adjacency.
The n-horizon cap is complete for a finite DAG; no reachability oracle is used. -/
namespace GreedyShortcuts.FiniteReachabilityDP
open SimpleGraph DirectedPaths FiniteDistanceDP CanonicalSegments
open LinearDistancePreservers.ConsistentTiebreaking
variable {n : ℕ}

def reaches (edge : Fin n → Fin n → Bool) (s t : Fin n) : Bool :=
  decide (value edge (fun _ _ => 1) (n+1) t n s < n+1)

@[simp] theorem unit_walkCost {s t : Fin n} (p : DWalk s t) :
    walkCost (fun _ _ => 1) p=p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih,Nat.add_comm]

theorem reaches_iff (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (s t : Fin n) : reaches edge s t=true ↔ Reachable G s t := by
  simp only [reaches,decide_eq_true_eq]
  constructor
  · intro hv
    obtain ⟨p,hp,_,_⟩ := value_sound edge (fun _ _ => 1) (n+1) t n s hv
    exact ⟨p,allowed_mono (fun u v h => (he u v).mp h) hp⟩
  · rintro ⟨p,hp⟩
    have hl : p.length<n := by
      simpa only [Fintype.card_fin] using (ChainDistance.Context.allowed_isPath hG p hp).length_lt
    have hpb := allowed_mono (fun u v h => (he u v).mpr h) hp
    have hv := value_le_walk edge (fun _ _ => 1) (n+1) t n p hpb (by omega)
    rw [unit_walkCost] at hv
    omega

end GreedyShortcuts.FiniteReachabilityDP
