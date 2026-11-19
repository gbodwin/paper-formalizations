import OnlineReachabilityPreservers.SteinerCompleteReplay
import OnlineReachabilityPreservers.SteinerDistanceTable

/-! Reuse the early distance table across the full sequence of arrival prefixes. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- One table and paired template serve all the prefixes. The second field
charges their original-graph searches once, outside the prefix list. -/
def completeSteinerPrefixSearchReplayWithDistanceTable (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) : List (Arcs V × ℕ) × ℕ :=
  let prepared := prepareEarlyDistanceTable G height sample
  let evaluate := completeSteinerDrawRunWithSearchWorkFromEarly G prepared.1 draw thin
  (D.inits.map evaluate,prepared.2)

theorem completeSteinerPrefixSearchReplayWithDistanceTable_eq (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) :
    completeSteinerPrefixSearchReplayWithDistanceTable G height sample draw thin D =
      (completeSteinerPrefixSearchReplay G height sample draw thin D,(distanceTableWithSearchWork G).2) := by
  simp only [completeSteinerPrefixSearchReplayWithDistanceTable, prepareEarlyDistanceTable_eq,
    completeSteinerPrefixSearchReplay]
  rfl

/-- Outputs agree at every prefix and the distance searches are charged once.
The bound counts the searches and successor tests reported by the evaluator. -/
theorem completeSteinerPrefixSearchReplayWithDistanceTable_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let n := Fintype.card V
    let m := G.card
    let out := completeSteinerPrefixSearchReplayWithDistanceTable G height sample draw thin D
    out.1.map Prod.fst = D.inits.map (completeSteinerDrawRun G height sample draw thin) ∧
      (out.1.map Prod.snd).sum + out.2 ≤
        (D.length+1)*completeSteinerSearchPolynomial n m height D.length+n^2*((n+1)*n*m) := by
  rw [completeSteinerPrefixSearchReplayWithDistanceTable_eq]
  have ordinary := completeSteinerPrefixSearchReplay_spec G height sample draw thin D feasible
  exact ⟨ordinary.1,Nat.add_le_add ordinary.2 (distanceTableWithSearchWork_bound G)⟩

end OnlineReachabilityPreservers
