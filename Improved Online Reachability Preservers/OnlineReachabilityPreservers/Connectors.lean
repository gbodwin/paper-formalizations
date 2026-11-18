import OnlineReachabilityPreservers.Components

/-! Sparse internal SCC connectors, using shortest-hop predecessor trees. -/

namespace OnlineReachabilityPreservers

open Finset Relation

variable {V : Type*} [LinearOrder V] [Fintype V]

private def hopCandidates (G : Arcs V) (s t : V) : Finset ℕ :=
  (range (Fintype.card V + 1)).filter (fun k => s ∈ reachIn G t k)

/-- Least successful reverse-search depth, or one more than the vertex count. -/
def hops (G : Arcs V) (s t : V) : ℕ :=
  (least? (hopCandidates G s t)).getD (Fintype.card V + 1)

theorem hops_spec {G : Arcs V} {s t : V} (h : Reach G s t) :
    hops G s t ≤ Fintype.card V ∧ s ∈ reachIn G t (hops G s t) := by
  have hmem : Fintype.card V ∈ hopCandidates G s t :=
    mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_self _), mem_reaches.mpr h⟩
  obtain ⟨k, hk⟩ := least?_some ⟨_, hmem⟩
  have hh : hops G s t = k := by simp [hops, hk]
  rw [hh]
  exact ⟨least?_le hk hmem, (mem_filter.mp (least?_mem hk)).2⟩

private theorem hops_le {G : Arcs V} {s t : V} {k : ℕ}
    (hk : k ≤ Fintype.card V) (hs : s ∈ reachIn G t k) :
    hops G s t ≤ k := by
  have hmem : k ∈ hopCandidates G s t :=
    mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hk), hs⟩
  obtain ⟨j, hj⟩ := least?_some ⟨k, hmem⟩
  have hh : hops G s t = j := by simp [hops, hj]
  rw [hh]
  exact least?_le hj hmem

private theorem hops_pos {G : Arcs V} {s t : V} (h : Reach G s t) (hne : s ≠ t) :
    0 < hops G s t := by
  have hm := (hops_spec h).2
  by_contra! hz
  have heq : hops G s t = 0 := Nat.eq_zero_of_le_zero hz
  rw [heq, reachIn, mem_singleton] at hm
  exact hne hm

/-- A reachable vertex different from the target has a successor on an earlier layer. -/
private theorem hopCandidates_nonempty (G : Arcs V) {s t : V} (h : Reach G s t)
    (hne : s ≠ t) : ((reachIn G t (hops G s t - 1)).filter (Edge G s)).Nonempty := by
  obtain ⟨hk, hm⟩ := hops_spec h
  have hpos := hops_pos h hne
  have hm' : s ∈ reachIn G t ((hops G s t - 1) + 1) := by
    rwa [Nat.sub_add_cancel hpos]
  rcases reachIn_succ.mp hm' with hs | ⟨v, he, hv⟩
  · have := hops_le ((Nat.sub_le _ _).trans hk) hs
    omega
  · exact ⟨v, mem_filter.mpr ⟨hv, he⟩⟩

theorem exists_decreasing_hop {G : Arcs V} {s t : V} (h : Reach G s t) (hne : s ≠ t) :
    ∃ v, Edge G s v ∧ Reach G v t ∧ hops G v t < hops G s t := by
  obtain ⟨v, hv⟩ := hopCandidates_nonempty G h hne
  obtain ⟨hr, he⟩ := mem_filter.mp hv
  have hk := hops_le ((Nat.sub_le _ _).trans (hops_spec h).1) hr
  have hd := hops_pos h hne
  exact ⟨v, he, reachIn_sound hr, by omega⟩

/-- For each nonroot vertex, choose one edge descending toward its SCC root. -/
private def towardRoot (G : Arcs V) (s : V) : Arcs V :=
  let t := componentLabel G s
  if s = t then ∅
  else match least? ((reachIn G t (hops G s t - 1)).filter (Edge G s)) with
    | some v => {(s, v)}
    | none => ∅

private theorem towardRoot_subset (G : Arcs V) (s : V) : towardRoot G s ⊆ G := by
  unfold towardRoot
  dsimp
  split
  · exact empty_subset _
  · split
    · rename_i v hv
      exact singleton_subset_iff.mpr (mem_filter.mp (least?_mem hv)).2
    · exact empty_subset _

private theorem towardRoot_card (G : Arcs V) (s : V) : (towardRoot G s).card ≤ 1 := by
  unfold towardRoot
  dsimp
  split
  · simp
  · split <;> simp

private theorem towardRoot_decreases (G : Arcs V) (s : V) (hne : s ≠ componentLabel G s) :
    ∃ v, Edge (towardRoot G s) s v ∧ componentLabel G v = componentLabel G s ∧
      hops G v (componentLabel G s) < hops G s (componentLabel G s) := by
  let t := componentLabel G s
  let k := hops G s t
  have hr : Reach G s t := (componentLabel_same s).1
  have hnonempty := hopCandidates_nonempty G hr (show s ≠ t from hne)
  have hprev : k - 1 ≤ Fintype.card V := (Nat.sub_le _ _).trans (hops_spec hr).1
  have hk' : 0 < k := hops_pos hr hne
  obtain ⟨v, hv⟩ := least?_some hnonempty
  obtain ⟨hvr, edge⟩ := mem_filter.mp (least?_mem hv)
  have hsc : SameComponent G v s :=
    ⟨(reachIn_sound hvr).trans (componentLabel_same s).2, .single edge⟩
  have hdist : hops G v t ≤ k - 1 := hops_le hprev hvr
  refine ⟨v, ?_, componentLabel_eq.mpr hsc, ?_⟩
  · have hv' : least? ((reachIn G (componentLabel G s)
        (hops G s (componentLabel G s) - 1)).filter (Edge G s)) = some v := hv
    simp [Edge, towardRoot, hv', hne]
  · change hops G v t < k
    omega

/-- The union of the in-trees for all SCCs, choosing at most one edge per vertex. -/
def inTrees (G : Arcs V) : Arcs V := univ.biUnion (towardRoot G)

theorem inTrees_subset (G : Arcs V) : inTrees G ⊆ G := by
  intro e he
  obtain ⟨u, _, hu⟩ := mem_biUnion.mp he
  exact towardRoot_subset G u hu

theorem inTrees_card (G : Arcs V) : (inTrees G).card ≤ Fintype.card V := by
  calc
    _ ≤ ∑ s : V, (towardRoot G s).card := card_biUnion_le
    _ ≤ ∑ _s : V, 1 := sum_le_sum (fun s _ => towardRoot_card G s)
    _ = _ := by simp

theorem inTrees_reach (G : Arcs V) (s : V) : Reach (inTrees G) s (componentLabel G s) := by
  have aux (k : ℕ) (u : V) (hu : hops G u (componentLabel G u) = k) :
      Reach (inTrees G) u (componentLabel G u) := by
    induction k using Nat.strong_induction_on generalizing u with
    | _ k ih =>
      by_cases h : u = componentLabel G u
      · rw [← h]
      · obtain ⟨v, edge, hv, hlt⟩ := towardRoot_decreases G u h
        have hlt' : hops G v (componentLabel G v) < k := by rwa [hv, ← hu]
        have hreach := ih _ hlt' v rfl
        rw [hv] at hreach
        apply hreach.head
        exact mem_biUnion.mpr ⟨u, mem_univ _, edge⟩
  exact aux _ s rfl

/-- One in-tree and one out-tree in each component. -/
def connectors (G : Arcs V) : Arcs V :=
  inTrees G ∪ reverseArcs (inTrees (reverseArcs G))

theorem connectors_subset (G : Arcs V) : connectors G ⊆ G := by
  apply union_subset (inTrees_subset G)
  simpa using reverseArcs_mono (inTrees_subset (reverseArcs G))

theorem connectors_card (G : Arcs V) : (connectors G).card ≤ 2 * Fintype.card V := by
  have hc := card_union_le (inTrees G) (reverseArcs (inTrees (reverseArcs G)))
  rw [reverseArcs_card] at hc
  unfold connectors
  have h₁ := inTrees_card G
  have h₂ := inTrees_card (reverseArcs G)
  omega

theorem connectors_reach {G : Arcs V} {u v : V} (eq : componentLabel G u = componentLabel G v) :
    Reach (connectors G) u v := by
  have h₁ : Reach (connectors G) u (componentLabel G u) :=
    reach_mono subset_union_left (inTrees_reach G u)
  have h₂ : Reach (connectors G) (componentLabel G v) v :=
    reach_mono subset_union_right (reach_reverseArcs.mpr (by simpa using inTrees_reach (reverseArcs G) v))
  exact h₁.trans (eq.symm ▸ h₂)

end OnlineReachabilityPreservers
