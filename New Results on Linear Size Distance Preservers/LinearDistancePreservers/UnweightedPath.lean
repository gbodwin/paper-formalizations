import LinearDistancePreservers.PathLowerBound
import LinearDistancePreservers.UnweightedPadding

/-! An unweighted native-distance path baseline for arbitrary exact sizes. -/
namespace LinearDistancePreservers.UnweightedPath
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

theorem path_rigid (k : ℕ) :
    UnweightedPadding.Rigid (ModularGraph.graph 1 k 1) (ModularGraph.terminals 1 k) := by
  intro H hH hp
  have hlayer : LayeredWalks.Layered (ModularGraph.graph 1 k 1) (fun v => (v.1.val : ℤ)) := by
    rintro u v ⟨b,a,hl,_⟩
    cases b
    · exact Or.inr hl
    · exact Or.inl hl
  have hinj : Function.Injective (fun v : ModularGraph.Vertex 1 k => (v.1.val : ℤ)) := by
    intro u v h
    apply Prod.ext
    · apply Fin.ext
      change (u.1.val : ℤ) = v.1.val at h
      exact_mod_cast h
    · exact Subsingleton.elim _ _
  apply UnweightedForcing.eq_of_covers
    (fun p : ZMod 1 × Fin 1 => ModularGraph.point p.1 p.2 0)
    (fun p : ZMod 1 × Fin 1 => ModularGraph.point p.1 p.2 (Fin.last k))
    (fun p => ModularGraph.canonicalWalk p.1 p.2)
  · intro p q hq
    apply PathLowerBound.unique_of_layer_injective (fun v => (v.1.val : ℤ)) hlayer hinj
      (ModularGraph.canonicalWalk p.1 p.2)
    · rw [ModularGraph.canonicalWalk_length]
      simp [ModularGraph.point]
    · exact hq
  · exact ModularGraph.canonical_covers
  · exact hH
  · intro p
    exact hp _ (ModularGraph.point_start_mem _ _) _ (ModularGraph.point_end_mem _ _)

/-- An endpoint pair forces all N-1 edges; enlarging terminals is harmless. -/
theorem path_lower_bound {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        H.edgeFinset.card = N-1 := by
  have hk : 0 < N-1 := by omega
  obtain ⟨G,S,hS,hr,hE⟩ := UnweightedPadding.pad
    (ModularGraph.graph 1 (N-1) 1) (ModularGraph.terminals 1 (N-1))
    (path_rigid (N-1)) (N := N) (T := T)
    (by simp [ModularGraph.Vertex,ZMod.card]; omega)
    (by rw [ModularGraph.terminals_card hk]; simpa using hT) hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  rw [hr H hH hp,hE,ModularGraph.graph_edge_count (by omega : 1 ≤ 1)]
  simp

end LinearDistancePreservers.UnweightedPath
