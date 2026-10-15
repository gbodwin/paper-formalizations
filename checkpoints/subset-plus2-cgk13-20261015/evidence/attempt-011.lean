import SlackSparsification.SubsetPlusTwoPaths
import SlackSparsification.SubsetPlusTwoCharging

/-! The sharp per-cluster missing-edge incidence bound behind CGK13 Lemma 6.
Unlike a mere three-vertices-per-cluster estimate, this uses retained intracluster edges. -/
namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph
open scoped BigOperators

/-- A set of positions spanning at most two with no consecutive pair has at most two elements. -/
theorem card_le_two_of_span_no_succ (I : Finset ℕ)
    (hspan : ∀ i ∈ I, ∀ j ∈ I, i ≤ j → j - i ≤ 2)
    (hgap : ∀ i ∈ I, i + 1 ∉ I) : I.card ≤ 2 := by
  by_cases hI : I.Nonempty
  · let m := I.min' hI
    have hm : m ∈ I := min'_mem I hI
    have hsub : I ⊆ {m, m + 2} := by
      intro j hj
      have hlo : m ≤ j := min'_le I j hj
      have hhi := hspan m hm j hj hlo
      have hne : j ≠ m + 1 := by intro h; exact hgap m hm (h ▸ hj)
      simp only [mem_insert, mem_singleton]
      omega
    exact (card_le_card hsub).trans (by simp)
  · simp [not_nonempty_iff_eq_empty.mp hI]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each cluster owns at most two source-endpoint incidences of missing steps. -/
theorem missing_source_incidence_le_two (G H : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V)
    (hd : ClusterDiameterTwo G C)
    (hintra : ∀ a ∈ C, ∀ b ∈ C, G.Adj a b → H.Adj a b)
    (M : Finset ℕ) (hM : ∀ i ∈ M, i < p.length ∧ ¬ H.Adj (p.getVert i) (p.getVert (i + 1))) :
    (M.filter fun i => p.getVert i ∈ C).card ≤ 2 := by
  apply card_le_two_of_span_no_succ
  · intro i hi j hj hij
    obtain ⟨hiM, hiC⟩ := mem_filter.mp hi
    obtain ⟨hjM, hjC⟩ := mem_filter.mp hj
    exact cluster_positions_span_two G p hp C hd i j
      ((mem_clusterPositions p C i).mpr ⟨(hM i hiM).1.le, hiC⟩)
      ((mem_clusterPositions p C j).mpr ⟨(hM j hjM).1.le, hjC⟩) hij
  · intro i hi hs
    obtain ⟨hiM, hiC⟩ := mem_filter.mp hi
    obtain ⟨_, hsC⟩ := mem_filter.mp hs
    exact (hM i hiM).2 (hintra _ hiC _ hsC (p.adj_getVert_succ (hM i hiM).1))

/-- The same bound holds for target-endpoint incidences, keeping edge indices explicit. -/
theorem missing_target_incidence_le_two (G H : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V)
    (hd : ClusterDiameterTwo G C)
    (hintra : ∀ a ∈ C, ∀ b ∈ C, G.Adj a b → H.Adj a b)
    (M : Finset ℕ) (hM : ∀ i ∈ M, i < p.length ∧ ¬ H.Adj (p.getVert i) (p.getVert (i + 1))) :
    (M.filter fun i => p.getVert (i + 1) ∈ C).card ≤ 2 := by
  apply card_le_two_of_span_no_succ
  · intro i hi j hj hij
    obtain ⟨hiM, hiC⟩ := mem_filter.mp hi
    obtain ⟨hjM, hjC⟩ := mem_filter.mp hj
    have h := cluster_positions_span_two G p hp C hd (i + 1) (j + 1)
      ((mem_clusterPositions p C (i + 1)).mpr ⟨by have := (hM i hiM).1; omega, hiC⟩)
      ((mem_clusterPositions p C (j + 1)).mpr ⟨by have := (hM j hjM).1; omega, hjC⟩)
      (by omega)
    omega
  · intro i hi hs
    obtain ⟨_, hiC⟩ := mem_filter.mp hi
    obtain ⟨hsM, hsC⟩ := mem_filter.mp hs
    exact (hM (i + 1) hsM).2
      (hintra _ hiC _ hsC (p.adj_getVert_succ (hM (i + 1) hsM).1))

/-- A concrete finite cluster family with diameter two and retained internal
edges contributes at most four endpoint incidences per cluster. -/
theorem missing_incidence_le_four (G H : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (C : Finset V)
    (hd : ClusterDiameterTwo G C)
    (hintra : ∀ a ∈ C, ∀ b ∈ C, G.Adj a b → H.Adj a b)
    (M : Finset ℕ) (hM : ∀ i ∈ M, i < p.length ∧ ¬ H.Adj (p.getVert i) (p.getVert (i + 1))) :
    (M.filter fun i => p.getVert i ∈ C).card +
      (M.filter fun i => p.getVert (i + 1) ∈ C).card ≤ 4 := by
  have hs := missing_source_incidence_le_two G H p hp C hd hintra M hM
  have ht := missing_target_incidence_le_two G H p hp C hd hintra M hM
  omega

/-- Exact Lemma 6 counting contract. The two cardinal-one hypotheses expose
unique cluster ownership for each missing endpoint; a clustering construction
must establish them from coverage and pairwise disjointness. -/
theorem missing_count_le_twice_clusters (G H : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.length = G.dist s t) (Cs : Finset (Finset V))
    (hd : ∀ C ∈ Cs, ClusterDiameterTwo G C)
    (hintra : ∀ C ∈ Cs, ∀ a ∈ C, ∀ b ∈ C, G.Adj a b → H.Adj a b)
    (M : Finset ℕ) (hM : ∀ i ∈ M, i < p.length ∧ ¬ H.Adj (p.getVert i) (p.getVert (i + 1)))
    (hs : ∀ i ∈ M, (Cs.filter fun C => p.getVert i ∈ C).card = 1)
    (ht : ∀ i ∈ M, (Cs.filter fun C => p.getVert (i + 1) ∈ C).card = 1) :
    M.card ≤ 2 * Cs.card := by
  have hsource : (∑ C ∈ Cs, (M.filter fun i => p.getVert i ∈ C).card) = M.card := by
    calc
      _ = ∑ i ∈ M, (Cs.filter fun C => p.getVert i ∈ C).card := by
        simp only [card_eq_sum_ones, sum_filter]
        exact sum_comm
      _ = ∑ _i ∈ M, 1 := sum_congr rfl hs
      _ = _ := by simp
  have htarget : (∑ C ∈ Cs, (M.filter fun i => p.getVert (i + 1) ∈ C).card) = M.card := by
    calc
      _ = ∑ i ∈ M, (Cs.filter fun C => p.getVert (i + 1) ∈ C).card := by
        simp only [card_eq_sum_ones, sum_filter]
        exact sum_comm
      _ = ∑ _i ∈ M, 1 := sum_congr rfl ht
      _ = _ := by simp
  have hbound : (∑ C ∈ Cs, ((M.filter fun i => p.getVert i ∈ C).card +
      (M.filter fun i => p.getVert (i + 1) ∈ C).card)) ≤ ∑ _C ∈ Cs, 4 := by
    apply sum_le_sum
    intro C hC
    exact missing_incidence_le_four G H p hp C (hd C hC) (hintra C hC) M hM
  rw [sum_add_distrib, hsource, htarget] at hbound
  simp only [sum_const, smul_eq_mul] at hbound
  omega

end SlackSparsification.SubsetPlusTwo
