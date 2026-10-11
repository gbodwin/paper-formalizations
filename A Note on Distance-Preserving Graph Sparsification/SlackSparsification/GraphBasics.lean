import SlackSparsification.Amplification
import LinearDistancePreservers.LazyTreeSelection
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! Actual graph semantics: unreachable distances use infinity. -/
namespace SlackSparsification
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def IsAdditiveSpanner (G H : SimpleGraph V) (P : Finset (V × V)) (k : ℕ) : Prop :=
  H ≤ G ∧ ∀ st ∈ P, H.edist st.1 st.2 ≤ G.edist st.1 st.2 + k

def IsReachabilityPreserver (G H : SimpleGraph V) (P : Finset (V × V)) : Prop :=
  H ≤ G ∧ ∀ st ∈ P, G.Reachable st.1 st.2 → H.Reachable st.1 st.2

theorem additive_mono {G H K : SimpleGraph V} {P : Finset (V × V)} {k : ℕ}
    (h : IsAdditiveSpanner G H P k) (hHK : H ≤ K) (hKG : K ≤ G) :
    IsAdditiveSpanner G K P k :=
  ⟨hKG, fun st hst => (edist_anti hHK).trans (h.2 st hst)⟩

theorem zero_additive_iff {G H : SimpleGraph V} {P : Finset (V × V)} :
    IsAdditiveSpanner G H P 0 ↔ H ≤ G ∧ ∀ st ∈ P, H.edist st.1 st.2 = G.edist st.1 st.2 := by
  constructor
  · rintro ⟨hHG, h⟩
    refine ⟨hHG, fun st hst => le_antisymm ?_ (edist_anti hHG)⟩
    simpa using h st hst
  · rintro ⟨hHG, h⟩
    exact ⟨hHG, fun st hst => by simp [h st hst]⟩

/-- Literally adding infinity makes every additive inequality true. This is
why reachability is a separate predicate, as intended by Definition 1. -/
theorem infinite_additive_vacuous (G H : SimpleGraph V) (s t : V) :
    H.edist s t ≤ G.edist s t + (⊤ : ℕ∞) := by simp

/-- An actual root-distance-preserving subgraph with at most n edges.
The pre-existing verified parent construction handles disconnected graphs. -/
theorem exists_shortest_path_tree (G : SimpleGraph V) (s : V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.edgeFinset.card ≤ Fintype.card V ∧
      ∀ v, T.edist s v = G.edist s v := by
  classical
  obtain ⟨f, hf⟩ := LinearDistancePreservers.LazyTreeSelection.exists_valid G s univ
  let T := LinearDistancePreservers.LazyTreeSelection.treeGraph hf
  let E : Finset (Sym2 V) := univ.image fun v => s(v, (f v).getD v)
  have hsub : T.edgeFinset ⊆ E := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have ha : T.Adj u v := by simpa using he
      rcases ha with ha | ha
      · exact mem_image.mpr ⟨v, mem_univ _, by simp [ha, Sym2.eq_swap]⟩
      · exact mem_image.mpr ⟨u, mem_univ _, by simp [ha]⟩
  refine ⟨T, LinearDistancePreservers.LazyTreeSelection.treeGraph_le hf,
    (card_le_card hsub).trans (card_image_le.trans (by simp)), ?_⟩
  intro v
  exact LinearDistancePreservers.LazyTreeSelection.tree_preserves hf (mem_univ v)

/-- Graph-level +2 routing through a root adjacent to a shortest-path vertex. -/
theorem plus_two_from_tree (G H : SimpleGraph V) (r s t u : V)
    (hroot : ∀ v, H.edist r v = G.edist r v)
    (hadj : G.Adj r u)
    (hsplit : G.edist s u + G.edist u t = G.edist s t) :
    H.edist s t ≤ G.edist s t + 2 := by
  have hru : G.edist r u = 1 := edist_eq_one_iff_adj.mpr hadj
  have hur : G.edist u r = 1 := edist_eq_one_iff_adj.mpr hadj.symm
  calc
    H.edist s t ≤ H.edist s r + H.edist r t := H.edist_triangle
    _ = G.edist s r + G.edist r t := by rw [H.edist_comm s r, hroot s, G.edist_comm r s, hroot t]
    _ ≤ (G.edist s u + 1) + (1 + G.edist u t) := by
      apply add_le_add
      · simpa [hur] using (G.edist_triangle (u := s) (v := u) (w := r))
      · simpa [hru] using (G.edist_triangle (u := r) (v := u) (w := t))
    _ = G.edist s t + 2 := by rw [← hsplit]; ac_rfl

end SlackSparsification
