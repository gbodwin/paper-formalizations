import LengthExpander.IncreasingPaths
import Mathlib.Data.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

/-- A finite family of nonempty edge sets can be hit using at most one edge per member. -/
theorem finite_hitting_set {I E : Type*} (F : Finset I) (E₀ : Finset E)
    (edges : I → Finset E) (hne : ∀ i ∈ F, (edges i).Nonempty)
    (hsub : ∀ i ∈ F, edges i ⊆ E₀) :
    ∃ S : Finset E, S ⊆ E₀ ∧ S.card ≤ F.card ∧
      ∀ i ∈ F, ∃ e ∈ S, e ∈ edges i := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨e,he⟩ := hne i (mem_insert_self i F)
    obtain ⟨S,hS,hcard,hhit⟩ := ih (fun j hj => hne j (mem_insert_of_mem hj))
      (fun j hj => hsub j (mem_insert_of_mem hj))
    refine ⟨insert e S, insert_subset (hsub i (mem_insert_self i F) he) hS, ?_, ?_⟩
    · exact (card_insert_le e S).trans (by simpa [card_insert_of_notMem hi] using Nat.add_le_add_right hcard 1)
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact ⟨e,mem_insert_self e S,he⟩
      · obtain ⟨d,hd,hdj⟩ := hhit j hj
        exact ⟨d,mem_insert_of_mem hd,hdj⟩

variable {V : Type*} {G : SimpleGraph V}

/-- Parallel-greedy structure is inherited by every edge-subgraph. -/
theorem parallelGreedy_mono {index : Sym2 V → ℕ} {s : ℕ}
    (H : IsParallelGreedy G index s) {G' : SimpleGraph V} (hG : G' ≤ G) :
    IsParallelGreedy G' index s := by
  constructor
  · intro u v z hu hv hi
    exact H.matching u v z (hG hu) (hG hv) hi
  · intro u v huv p hp he
    apply H.earlierFar u v (hG huv) (p.mapLe hG)
    · simpa only [Walk.length_mapLe] using hp
    · simpa only [Walk.edges_mapLe_eq_edges] using he

variable [Fintype V]

/-- One finite set contains all oriented fixed-length monotone walks. -/
noncomputable def allMonotoneWalks (G : SimpleGraph V) (index : Sym2 V → ℕ) (r : ℕ) :
    Finset ((u : V) × (v : V) × G.Walk u v) := by
  classical
  exact univ.sigma (fun u => univ.sigma (fun v => monotoneWalks G index r u v))

@[simp] theorem mem_allMonotoneWalks {index : Sym2 V → ℕ} {r : ℕ}
    {w : (u : V) × (v : V) × G.Walk u v} :
    w ∈ allMonotoneWalks G index r ↔ w.2.2.length = r ∧ Increasing index w.2.2 := by
  classical
  simp [allMonotoneWalks]

@[simp] theorem card_allMonotoneWalks (index : Sym2 V → ℕ) (r : ℕ) :
    (allMonotoneWalks G index r).card = monotoneCount G index r := by
  classical
  simp [allMonotoneWalks, card_sigma, monotoneCount]

/-- Delete at most one edge per increasing walk to destroy every r-edge increasing walk. -/
theorem exists_monotone_blocker (index : Sym2 V → ℕ) {r : ℕ} (hr : 0 < r) :
    ∃ S : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ S.card ≤ monotoneCount G index r ∧
      ∀ u v (p : G.Walk u v), p.length = r → Increasing index p →
        ∃ e ∈ S, e ∈ p.edges := by
  classical
  have hne : ∀ w ∈ allMonotoneWalks G index r, w.2.2.edges.toFinset.Nonempty := by
    intro w hw
    have hl := (mem_allMonotoneWalks.mp hw).1
    have hp : w.2.2.edges ≠ [] := by
      intro he
      have := congrArg List.length he
      simp only [Walk.length_edges, List.length_nil] at this
      omega
    cases he : w.2.2.edges with
    | nil => exact (hp he).elim
    | cons e l => exact ⟨e,by simp [he]⟩
  have hsub : ∀ w ∈ allMonotoneWalks G index r, w.2.2.edges.toFinset ⊆ G.edgeFinset := by
    intro w hw e he
    exact G.mem_edgeFinset.mpr (w.2.2.edges_subset_edgeSet (by simpa using he))
  obtain ⟨S,hS,hcard,hhit⟩ := finite_hitting_set (allMonotoneWalks G index r) G.edgeFinset
    (fun w => w.2.2.edges.toFinset) hne hsub
  refine ⟨S,hS,by simpa using hcard,?_⟩
  intro u v p hp hi
  obtain ⟨e,he,hep⟩ := hhit ⟨u,v,p⟩ (mem_allMonotoneWalks.mpr ⟨hp,hi⟩)
  exact ⟨e,he,by simpa using hep⟩

/-- Quantitative deletion lemma. If too few monotone walks existed, deleting
one edge from each would leave enough edges for the actual hiker construction. -/
theorem deletion_counting [Nonempty V] {index : Sym2 V → ℕ}
    (H : MatchingLabels G index) {r : ℕ} (hr : 0 < r) :
    2 * G.edgeFinset.card < Fintype.card V * r + 2 * monotoneCount G index r := by
  classical
  obtain ⟨S,hS,hcard,hhit⟩ := exists_monotone_blocker (G := G) index hr
  let G' := G.deleteEdges (S : Set (Sym2 V))
  have hG : G' ≤ G := G.deleteEdges_le S
  have hmatching : MatchingLabels G' index := by
    intro u v z hu hv hi
    exact H u v z (hG hu) (hG hv) hi
  have hedges : G'.edgeFinset.card + S.card = G.edgeFinset.card := by
    change (G.deleteEdges (S : Set (Sym2 V))).edgeFinset.card + S.card = _
    rw [G.edgeFinset_deleteEdges S]
    exact card_sdiff_add_card_eq_card hS
  by_contra hn
  have hm : Fintype.card V * r ≤ 2 * G'.edgeFinset.card := by omega
  obtain ⟨u,v,p,hp,hlen⟩ := weak_counting_walk hmatching r (by convert hm using 1; congr 2; ext e; simp only [mem_edgeFinset])
  obtain ⟨e,heS,hep⟩ := hhit u v (p.mapLe hG)
    (by simpa only [Walk.length_mapLe] using hlen)
    (by simpa only [Increasing, Walk.edges_mapLe_eq_edges] using hp)
  have heG' : e ∈ G'.edgeSet := p.edges_subset_edgeSet
    (by simpa only [Walk.edges_mapLe_eq_edges] using hep)
  have henot : e ∉ S := (G.edgeSet_deleteEdges S ▸ heG').2
  exact henot heS

/-- Explicit medium counting: at density m ≥ nr, at least n/2 walks exist.
In fact the proved lower bound is nr/2, which is at least n/2 for r ≥ 1. -/
theorem medium_counting [Nonempty V] {index : Sym2 V → ℕ}
    (H : MatchingLabels G index) {r : ℕ} (hr : 0 < r)
    (hm : Fintype.card V * r ≤ G.edgeFinset.card) :
    Fintype.card V * r < 2 * monotoneCount G index r := by
  have := deletion_counting H hr
  omega

end LengthExpander
