import LinearDistancePreservers.UnweightedPadding

/-! The complete-graph baseline for Theorem 4. Exact padding gives a
witness with any prescribed positive terminal count up to the vertex
count. This handles lower bounds dominated by choose(T,2); it does not
supply the sharp lattice-direction estimate or a superquadratic bound. -/
namespace LinearDistancePreservers.UnweightedClique
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

/-- Preserving every distance in a complete graph forces every edge. -/
theorem complete_rigid {V : Type*} [Fintype V] [DecidableEq V] :
    UnweightedPadding.Rigid (⊤ : SimpleGraph V) univ := by
  intro H _ hp
  apply le_antisymm le_top
  intro u v huv
  apply edist_eq_one_iff_adj.mp
  exact (hp u (mem_univ u) v (mem_univ v)).trans (edist_eq_one_iff_adj.mpr huv)

/-- An actual unweighted graph with N vertices and T terminals forces
exactly choose(T,2) edges. All terminal-pair distances are native edist. -/
theorem clique_lower_bound {N T : ℕ} (hT : 0 < T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = T.choose 2 := by
  classical
  letI : NeZero T := ⟨Nat.ne_of_gt hT⟩
  -- Keep the library theorem's inferred finite-set instance until the
  -- Nat.card conversion below, avoiding a definitional instance comparison.
  have he := card_edgeFinset_top_eq_card_choose_two (V := Fin T)
  simp only [Fintype.card_fin] at he
  obtain ⟨G,S,hS,hG,hE⟩ := UnweightedPadding.pad
    (⊤ : SimpleGraph (Fin T)) univ complete_rigid
    (by simpa using hTN) (by simp) hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  have heq : H = G := hG H hH hp
  subst H
  simp only [edgeFinset,Set.toFinset_card,Fintype.card_eq_nat_card] at hE he ⊢
  exact hE.trans he

end LinearDistancePreservers.UnweightedClique
