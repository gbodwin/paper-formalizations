import SlackSparsification.SubsetPlusTwoCore

/-! Actual shortest-path occurrence contracts for CGK13. Path-restricted
prefix/suffix minima are deliberately distinct from global clusterEDist. -/
namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph
variable {V : Type*}

noncomputable def clusterPositions {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) (C : Finset V) : Finset ℕ := by
  classical
  exact (range (p.length + 1)).filter fun i => p.getVert i ∈ C

noncomputable def prefixDistance {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) (C : Finset V) : ℕ∞ :=
  (clusterPositions p C).inf fun i => (i : ℕ∞)

noncomputable def suffixDistance {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) (C : Finset V) : ℕ∞ :=
  (clusterPositions p C).inf fun i => ((p.length - i : ℕ) : ℕ∞)

@[simp] theorem mem_clusterPositions {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) (C : Finset V) (i : ℕ) :
    i ∈ clusterPositions p C ↔ i ≤ p.length ∧ p.getVert i ∈ C := by
  classical
  simp [clusterPositions]

variable [Fintype V] [DecidableEq V]

theorem shortest_prefix_edist (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (i : ℕ) (hi : i ≤ p.length) :
    G.edist s (p.getVert i) = (i : ℕ∞) := by
  have h := SlackSparsification.shortest_index_distance G p hp 0 i (Nat.zero_le _) hi
  have hr := (p.take i).reachable.coe_dist_eq_edist
  simpa using hr.symm.trans (by exact_mod_cast (by simpa using h : G.dist s (p.getVert i) = i))

theorem shortest_suffix_edist (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (i : ℕ) (hi : i ≤ p.length) :
    G.edist t (p.getVert i) = ((p.length - i : ℕ) : ℕ∞) := by
  have h := SlackSparsification.shortest_index_distance G p hp i p.length hi le_rfl
  have hr := (p.drop i).reachable.coe_dist_eq_edist
  rw [G.edist_comm]
  exact hr.symm.trans (by exact_mod_cast (by simpa using h : G.dist (p.getVert i) t = p.length - i))

/-- The global minimum is no larger than the restricted prefix minimum. -/
theorem global_le_prefix (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V) :
    clusterEDist G s C ≤ prefixDistance p C := by
  apply Finset.le_inf
  intro i hi
  obtain ⟨hil, hic⟩ := (mem_clusterPositions p C i).mp hi
  exact (clusterEDist_le G s C hic).trans_eq (shortest_prefix_edist G p hp i hil)

/-- A visited cluster's restricted minimum is at most global minimum +2. -/
theorem prefix_le_global_add_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V)
    (hd : ClusterDiameterTwo G C) (hv : (clusterPositions p C).Nonempty) :
    prefixDistance p C ≤ clusterEDist G s C + 2 := by
  obtain ⟨i, hi⟩ := hv
  obtain ⟨hil, hic⟩ := (mem_clusterPositions p C i).mp hi
  calc
    _ ≤ (i : ℕ∞) := Finset.inf_le hi
    _ = G.edist s (p.getVert i) := (shortest_prefix_edist G p hp i hil).symm
    _ ≤ _ := member_edist_le_cluster_add_two G s C hd hic

theorem global_le_suffix (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V) :
    clusterEDist G t C ≤ suffixDistance p C := by
  apply Finset.le_inf
  intro i hi
  obtain ⟨hil, hic⟩ := (mem_clusterPositions p C i).mp hi
  exact (clusterEDist_le G t C hic).trans_eq (shortest_suffix_edist G p hp i hil)

theorem suffix_le_global_add_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V)
    (hd : ClusterDiameterTwo G C) (hv : (clusterPositions p C).Nonempty) :
    suffixDistance p C ≤ clusterEDist G t C + 2 := by
  obtain ⟨i, hi⟩ := hv
  obtain ⟨hil, hic⟩ := (mem_clusterPositions p C i).mp hi
  calc
    _ ≤ ((p.length - i : ℕ) : ℕ∞) := Finset.inf_le (f := fun j => ((p.length - j : ℕ) : ℕ∞)) hi
    _ = G.edist t (p.getVert i) := (shortest_suffix_edist G p hp i hil).symm
    _ ≤ _ := member_edist_le_cluster_add_two G t C hd hic

omit [Fintype V] [DecidableEq V] in
/-- Lemma 7 routing with the actual comparison used by the buying rule.
The two inequalities can hold even when neither distance equals the global minimum. -/
theorem rejected_cluster_route (G H : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V)
    (hd : ClusterDiameterTwo H C) (hv : (clusterPositions p C).Nonempty)
    (hs : clusterEDist H s C ≤ prefixDistance p C)
    (ht : clusterEDist H t C ≤ suffixDistance p C) :
    H.edist s t ≤ G.edist s t + 2 := by
  obtain ⟨i, hi⟩ := hv
  obtain ⟨hil, hic⟩ := (mem_clusterPositions p C i).mp hi
  apply rejection_route G H s t C ⟨_, hic⟩ hd i (p.length - i)
  · exact hs.trans (Finset.inf_le hi)
  · exact ht.trans (Finset.inf_le hi)
  · rw [Nat.add_sub_of_le hil, hp]
    exact p.reachable.coe_dist_eq_edist

/-- Diameter two forces any two occurrence indices to differ by at most two. -/
theorem cluster_positions_span_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V)
    (hd : ClusterDiameterTwo G C) (i j : ℕ)
    (hi : i ∈ clusterPositions p C) (hj : j ∈ clusterPositions p C) (hij : i ≤ j) :
    j - i ≤ 2 := by
  obtain ⟨_, hic⟩ := (mem_clusterPositions p C i).mp hi
  obtain ⟨hjl, hjc⟩ := (mem_clusterPositions p C j).mp hj
  have h := (G.natCast_dist_le_edist (u := p.getVert i) (v := p.getVert j)).trans (hd _ hic _ hjc)
  rw [SlackSparsification.shortest_index_distance G p hp i j hij hjl] at h
  exact_mod_cast h

/-- The first counting ingredient of CGK13 Lemma 6. The sharper four-incidence
bound additionally needs the missing-edge property and consecutive triple case. -/
theorem cluster_positions_card_le_three (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V)
    (hd : ClusterDiameterTwo G C) : (clusterPositions p C).card ≤ 3 := by
  apply SlackSparsification.card_le_three_of_span
  exact fun i hi j hj hij => cluster_positions_span_two G p hp C hd i j hi hj hij

end SlackSparsification.SubsetPlusTwo
