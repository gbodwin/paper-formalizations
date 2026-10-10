import GreedyShortcuts.DirectedMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Corollary 5.3's finite disjoint-chain application. The constant-hop path
supershortcut construction is an explicitly supplied cited background witness;
its embedding, union, reachability preservation and size accounting are proved. -/
namespace GreedyShortcuts.ChainUnion

open Finset SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A directed chain is an injectively indexed sequence in the reachability
relation. It need not be a path of original edges. -/
structure Chain (G : V → V → Prop) where
  length : ℕ
  node : Fin length → V
  injective : Function.Injective node
  forward : ∀ i j,i < j → Reachable G (node i) (node j)

def Chain.support {G : V → V → Prop} (C : Chain G) : Finset V := Finset.univ.image C.node

theorem Chain.support_card {G : V → V → Prop} (C : Chain G) : C.support.card = C.length := by
  rw [Chain.support,Finset.card_image_of_injective _ C.injective]
  simp

theorem Chain.length_le {G : V → V → Prop} (C : Chain G) : C.length ≤ Fintype.card V := by
  rw [← C.support_card]
  exact Finset.card_le_univ _

/-- Uniform finite interface for the cited forward path super-shortcut lemma.
The original consecutive path edges may be included in `edges`; their cost is
therefore included in K*m. All inserted edges point forward. -/
structure PathWitness (m K : ℕ) where
  edges : Finset (Fin m × Fin m)
  forward : ∀ e ∈ edges,e.1 < e.2
  card_le : edges.card ≤ K*m
  short : ∀ i j : Fin m,i ≤ j →
    ∃ p : DWalk i j, Allowed (fun u v => (u,v) ∈ edges) p ∧ p.length ≤ 4

/-- The background interface is nonvacuous: a forward clique gives a simple
quadratic witness. The cited path theorem supplies the much smaller K. -/
theorem pathWitness_nonempty (m K : ℕ) (hm : m ≤ K) : Nonempty (PathWitness m K) := by
  classical
  let J := (Finset.univ : Finset (Fin m × Fin m)).filter (fun e => e.1 < e.2)
  refine ⟨{ edges := J, forward := ?_, card_le := ?_, short := ?_ }⟩
  · intro e he
    exact (Finset.mem_filter.mp he).2
  · calc
      J.card ≤ (Finset.univ : Finset (Fin m × Fin m)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = m*m := by simp
      _ ≤ K*m := Nat.mul_le_mul_right m hm
  · intro i j hij
    rcases lt_or_eq_of_le hij with hlt | rfl
    · have ha : (⊤ : SimpleGraph (Fin m)).Adj i j := by simpa using ne_of_lt hlt
      refine ⟨.cons ha .nil,?_,by simp⟩
      exact (allowed_cons _ ha .nil).mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩,allowed_nil _ _⟩
    · exact ⟨.nil,allowed_nil _ _,by simp⟩

def mappedEdges {G : V → V → Prop} (C : Chain G) {K : ℕ} (W : PathWitness C.length K) :
    Finset (V × V) := DirectedMap.edges C.node W.edges

theorem mappedEdges_subset {G : V → V → Prop} (C : Chain G) {K : ℕ}
    (W : PathWitness C.length K) : mappedEdges C W ⊆ candidates G := by
  intro e he
  obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp he
  have hf := W.forward ij hij
  apply (mem_candidates G _).mpr
  exact ⟨fun he => (ne_of_lt hf) (C.injective he),C.forward _ _ hf⟩

theorem mappedEdges_hop {G : V → V → Prop} (C : Chain G) {K : ℕ}
    (W : PathWitness C.length K) (i j : Fin C.length) (hij : i ≤ j) :
    hopDist (augment G (mappedEdges C W)) (C.node i) (C.node j) ≤ 4 := by
  obtain ⟨p,hp,hl⟩ := W.short i j hij
  have hh := hopDist_le_walk (augment G (mappedEdges C W)) (p.map (DirectedMap.hom C.node C.injective))
    (DirectedMap.allowed_map C.node C.injective
      (fun u v huv => Or.inr (DirectedMap.mem_edges C.node W.edges huv)) p hp)
  exact (show hopDist (augment G (mappedEdges C W)) (C.node i) (C.node j) ≤ p.length by
    simpa [DirectedMap.hom] using hh).trans hl

section Family
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem disjoint_length_sum {G : V → V → Prop} (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support)) :
    (∑ i,(C i).length) ≤ Fintype.card V := by
  calc
    (∑ i,(C i).length) = ∑ i,(C i).support.card := by simp only [Chain.support_card]
    _ = ((Finset.univ : Finset I).biUnion (fun i => (C i).support)).card := by
      symm
      apply Finset.card_biUnion
      intro i hi j hj hne
      exact hdisj hne
    _ ≤ _ := Finset.card_le_univ _

/-- The derived chain-family result, with its necessary forward-pair qualifier.
The proof constructs the union and does not assume this corollary as input. -/
theorem supershortcut_union {G : V → V → Prop} (C : I → Chain G)
    (hdisj : Pairwise (fun i j => Disjoint (C i).support (C j).support)) (K : ℕ)
    (background : ∀ m ≤ Fintype.card V, Nonempty (PathWitness m K)) :
    ∃ H : Finset (V × V), H ⊆ candidates G ∧ H.card ≤ K*Fintype.card V ∧
      ∀ c (i j : Fin (C c).length), i ≤ j →
        hopDist (augment G H) ((C c).node i) ((C c).node j) ≤ 4 := by
  classical
  let W := fun c => Classical.choice (background (C c).length (C c).length_le)
  let H := (Finset.univ : Finset I).biUnion (fun c => mappedEdges (C c) (W c))
  have hlocal : ∀ c,mappedEdges (C c) (W c) ⊆ H := by
    intro c e he
    exact Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,he⟩
  refine ⟨H,?_,?_,?_⟩
  · intro e he
    obtain ⟨c,hc,he⟩ := Finset.mem_biUnion.mp he
    exact mappedEdges_subset (C c) (W c) he
  · calc
      H.card ≤ ∑ c,(mappedEdges (C c) (W c)).card := Finset.card_biUnion_le
      _ ≤ ∑ c,K*(C c).length := Finset.sum_le_sum (fun c _ =>
        (DirectedMap.edges_card_le _ _).trans (W c).card_le)
      _ = K*∑ c,(C c).length := (Finset.mul_sum _ _ _).symm
      _ ≤ K*Fintype.card V := Nat.mul_le_mul_left K (disjoint_length_sum C hdisj)
  · intro c i j hij
    have hr : Reachable G ((C c).node i) ((C c).node j) := by
      rcases lt_or_eq_of_le hij with hlt | rfl
      · exact (C c).forward i j hlt
      · exact reachable_refl G _
    exact (hopDist_augment_antitone G (hlocal c) hr).trans (mappedEdges_hop (C c) (W c) i j hij)

end Family
end GreedyShortcuts.ChainUnion
