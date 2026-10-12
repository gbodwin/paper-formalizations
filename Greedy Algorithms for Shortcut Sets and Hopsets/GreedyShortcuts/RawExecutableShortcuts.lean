import GreedyShortcuts.ComputedChainContext
import GreedyShortcuts.ChainExecutableMoment

/-! The complete finite DAG shortcut construction from a Boolean adjacency
input: compute the disjoint chain cover, compute its four-hop preprocessing,
and run the deterministic original-objective greedy stage. No chain, cover,
reachability, normalized-distance or preprocessing witness is supplied. -/
namespace GreedyShortcuts.RawExecutableShortcuts
open Finset SimpleGraph DirectedPaths CanonicalSegments ComputedChainPacking
open LinearDistancePreservers.ConsistentTiebreaking
variable {n : ℕ}

def data (edge : Fin n → Fin n → Bool) (hG : Acyclic (fun u v => edge u v=true)) (r : ℕ) :=
  context (fun u v => edge u v=true) hG edge (fun _ _ => Iff.rfl) r

def output (edge : Fin n → Fin n → Bool) (hG : Acyclic (fun u v => edge u v=true)) (r D : ℕ) :
    Finset (Fin n×Fin n) :=
  let T := data edge hG r
  T.base∪ChainExecutableGreedy.output T edge D

theorem output_legal (edge : Fin n → Fin n → Bool) (hG : Acyclic (fun u v => edge u v=true))
    (r D : ℕ) (hD : 2≤D) : output edge hG r D⊆candidates (fun u v => edge u v=true) := by
  apply Finset.union_subset
  · exact ChainNormalization.union_subset (data edge hG r).chains (data edge hG r).witnesses
  · exact ChainExecutableGreedy.output_legal (data edge hG r) edge (fun _ _ => Iff.rfl) D hD

theorem output_hop_bound (edge : Fin n → Fin n → Bool)
    (hG : Acyclic (fun u v => edge u v=true)) (r D : ℕ) (hr : 0<r) (hD : 2≤D)
    {s t : Fin n} (hst : Reachable (fun u v => edge u v=true) s t) :
    ∃p : DWalk s t,Allowed (augment (fun u v => edge u v=true) (output edge hG r D)) p ∧
      p.length≤2*(r-1)+5*D+4 :=
  ChainExecutableGreedy.output_hop_bound (data edge hG r) edge (fun _ _ => Iff.rfl) D hD
    (context_cover _ hG edge (fun _ _ => Iff.rfl) r hr) hst

/-- The existing weaker moment-size bound now applies to this raw-input output.
The actual chain count is bounded by n/r; no nearlinear rate is assumed. -/
theorem output_card_moment (edge : Fin n → Fin n → Bool)
    (hG : Acyclic (fun u v => edge u v=true)) (r D R : ℕ)
    (hr : 0<r) (hD : 3≤D) (hR : 0<R) (hscale : R^3≤D^2) :
    (output edge hG r D).card≤(6*PathFour.computedHeight r+1)*n+
      2*(256*(n*(n/r))/R^2+1) := by
  have hm : (lists edge r).length≤n/r := (Nat.le_div_iff_mul_le hr).mpr
    (chain_count _ hG edge (fun _ _ => Iff.rfl) r)
  have hh := ChainExecutableGreedy.shortcuts_card_moment (data edge hG r) edge
    (fun _ _ => Iff.rfl) D hD R hR hscale
  exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.add_le_add_right
    (Nat.div_le_div_right (Nat.mul_le_mul_left 256 (Nat.mul_le_mul_left n hm))) 1)) _)

end GreedyShortcuts.RawExecutableShortcuts
