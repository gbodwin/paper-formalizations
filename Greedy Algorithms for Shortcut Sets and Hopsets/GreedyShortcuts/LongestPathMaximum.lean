import GreedyShortcuts.FiniteLongestPathDP
import GreedyShortcuts.ChainValidity

/-! A concrete longest enabled path in a finite DAG. The n horizon is complete;
selection is over the materialized vertex rows and returns their actual list. -/
namespace GreedyShortcuts.FiniteLongestPathDP
open SimpleGraph DirectedPaths CanonicalSegments
open LinearDistancePreservers.ConsistentTiebreaking
variable {n : ℕ}

def maximum (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool) : List (Fin n) :=
  longest (List.ofFn (fun u : Fin n => path edge enabled n u))

theorem maximum_sound (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool)
    (hm : maximum edge enabled≠[]) :
    ∃s t,∃p : DWalk s t,Allowed (fun a b => edge a b=true) p ∧
      (∀v∈p.support,enabled v=true) ∧ p.support=maximum edge enabled := by
  obtain ⟨u,hu⟩ := List.mem_ofFn.mp ((longest_mem_or_empty
    (List.ofFn (fun u : Fin n => path edge enabled n u))).resolve_left hm)
  obtain ⟨t,p,hp,hen,he,_⟩ := path_sound edge enabled n u (by rw [hu];exact hm)
  exact ⟨u,t,p,hp,hen,he.trans hu⟩

theorem maximum_complete (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (enabled : Fin n → Bool) {s t : Fin n} (p : DWalk s t)
    (hp : Allowed G p) (hen : ∀v∈p.support,enabled v=true) :
    p.length+1≤(maximum edge enabled).length := by
  have hl : p.length<n := by
    simpa only [Fintype.card_fin] using (ChainDistance.Context.allowed_isPath hG p hp).length_lt
  have hpb := allowed_mono (fun u v h => (he u v).mpr h) hp
  exact (path_longest edge enabled n p hpb hen (by omega)).trans
    (le_longest (List.mem_ofFn.mpr ⟨s,rfl⟩))

theorem maximum_nodup (G : Fin n → Fin n → Prop) (hG : Acyclic G)
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ G u v)
    (enabled : Fin n → Bool) : (maximum edge enabled).Nodup := by
  by_cases hm : maximum edge enabled=[]
  · simp [hm]
  · obtain ⟨s,t,p,hp,_,hs⟩ := maximum_sound edge enabled hm
    have hg := allowed_mono (fun u v h => (he u v).mp h) hp
    rw [←hs]
    exact (ChainDistance.Context.allowed_isPath hG p hg).support_nodup

theorem maximum_enabled (edge : Fin n → Fin n → Bool) (enabled : Fin n → Bool)
    {v : Fin n} (hv : v∈maximum edge enabled) : enabled v=true := by
  have hm : maximum edge enabled≠[] := List.ne_nil_of_mem hv
  obtain ⟨s,t,p,_,hen,hs⟩ := maximum_sound edge enabled hm
  exact hen v (hs ▸ hv)

end GreedyShortcuts.FiniteLongestPathDP
