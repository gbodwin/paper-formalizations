import LightSpanners.UnitCycle
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace LightSpanners
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {r : V} {n : ℕ}

/-- Consecutive positions in a nondegenerate closed walk remain adjacent at
its wraparound. -/
theorem closed_walk_getVert_add_one (p : G.Walk r r) (hlen : p.length = n + 3)
    (i : Fin (n + 3)) : G.Adj (p.getVert i.val) (p.getVert (i + 1).val) := by
  have hi : i.val < p.length := by omega
  have ha := p.adj_getVert_succ hi
  by_cases hlast : i.val + 1 = n + 3
  · have hval : (i + 1 : Fin (n + 3)).val = 0 := by
      simp [Fin.val_add, hlast]
    have hend : p.getVert (i.val + 1) = r := by
      rw [hlast, ← hlen, Walk.getVert_length]
    simpa only [hval, Walk.getVert_zero, hend] using ha
  · have hlt : i.val + 1 < n + 3 := by omega
    have hval : (i + 1 : Fin (n + 3)).val = i.val + 1 := by
      simp [Fin.val_add, Nat.mod_eq_of_lt hlt]
    simpa only [hval] using ha

/-- The cycle on the positions of a closed walk maps to the original graph. -/
def closedWalkCycleHom (p : G.Walk r r) (hlen : p.length = n + 3) :
    cycleGraph (n + 3) →g G where
  toFun i := p.getVert i.val
  map_rel' := by
    intro a b hab
    rcases cycleGraph_adj.mp hab with h | h
    · have heq : a = b + 1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h)
      subst a
      exact (closed_walk_getVert_add_one p hlen b).symm
    · have heq : b = a + 1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h)
      subst b
      exact closed_walk_getVert_add_one p hlen a

/-- A spanning closed walk gives a surjective vertex projection from its
position cycle, including when vertices repeat in the walk. -/
theorem closedWalkCycleHom_surjective (p : G.Walk r r) (hlen : p.length = n + 3)
    (hcover : ∀ v : V, v ∈ p.support) : Function.Surjective (closedWalkCycleHom p hlen) := by
  classical
  intro v
  let i := p.support.idxOf v
  have hi : i < p.support.length := List.idxOf_lt_length_iff.mpr (hcover v)
  have hget : p.getVert i = v := p.getVert_support_idxOf (hcover v)
  have hle : i ≤ p.length := by
    simp only [Walk.length_support] at hi
    omega
  by_cases hlt : i < p.length
  · exact ⟨⟨i, by omega⟩, hget⟩
  · have heq : i = p.length := by omega
    refine ⟨0, ?_⟩
    change p.getVert 0 = v
    simpa only [heq, Walk.getVert_length, Walk.getVert_zero] using hget

/-- The canonical finite cycle is an actual unit spanning cycle. -/
def canonicalUnitSpanningCycle (n : ℕ) :
    UnitSpanningCycle (cycleGraph (n + 3)) (fun _ => 1) where
  base := 0
  cycle := cycleGraph.cycle n
  hamiltonian := Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    ⟨cycleGraph.isCycle_cycle, by simp⟩
  unit := by simp
  lower := by simp

/-- In a connected graph consisting of cycles, any cycle visits every vertex. -/
theorem cycle_hamiltonian_of_connected_isCycles [Fintype V] [DecidableEq V]
    [LocallyFinite G] (hconn : G.Connected) (hcyc : G.IsCycles)
    (p : G.Walk r r) (hp : p.IsCycle) : p.IsHamiltonianCycle := by
  have hprop : ∀ {a b : V}, (q : G.Walk a b) → a ∈ p.support → b ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | @cons a b c hab q ih =>
      intro ha
      apply ih
      have hsub := (hp.adj_toSubgraph_iff_of_isCycles hcyc
        (p.mem_verts_toSubgraph.mpr ha) b).mpr hab
      exact p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hsub.symm)
  have hcover : ∀ v : V, v ∈ p.support := by
    intro v
    obtain ⟨q⟩ := hconn r v
    exact hprop q (Walk.start_mem_support p)
  apply Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mpr
  refine ⟨hp, fun v => ?_⟩
  apply List.count_eq_one_of_mem ((Walk.isCycle_def p).mp hp).2.2
  rcases (p.mem_support_iff).mp (hcover v) with heq | hv
  · subst v
    exact Walk.end_mem_tail_support hp.not_nil
  · exact hv

/-- The position cycle alone has weighted girth equal to its number of vertices. -/
theorem cycleGraph_weightedGirthAbove {g : ℝ} (hg : g < n + 3) :
    WeightedGirthAbove (cycleGraph (n + 3)) (fun _ => 1) g := by
  intro r p hp e he
  have hcyc : (cycleGraph (n + 3)).IsCycles := by
    intro v _
    rw [ncard_neighborSet, cycleGraph_degree_three_le]
  have hham := cycle_hamiltonian_of_connected_isCycles cycleGraph_connected hcyc p hp
  rw [walkWeight_eq_length_of_unit (fun _ => 1) p (by simp), hham.length_eq]
  norm_num only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, mul_one]
  linarith

end LightSpanners
