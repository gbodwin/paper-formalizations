import OnlineReachabilityPreservers.SteinerCompleteReplay
import OnlineReachabilityPreservers.SteinerDistanceTable

/-! Reuse the early distance table across the full sequence of arrival prefixes. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Share the distance table and paired template across all prefixes, and
report the arc inspections and template key comparisons separately. -/
def completeSteinerPrefixSearchReplayWithTemplateWork (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ :=
  let prepared := prepareEarlyDistanceTableWithTemplateWork G height sample
  let evaluate := completeSteinerDrawRunWithSearchWorkFromEarly G prepared.1 draw thin
  (D.inits.map evaluate,prepared.2.1,prepared.2.2)

theorem completeSteinerPrefixSearchReplayWithTemplateWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) :
    let out := completeSteinerPrefixSearchReplayWithTemplateWork G height sample draw thin D
    let n := Fintype.card V
    out.1 = completeSteinerPrefixSearchReplay G height sample draw thin D ∧
      out.2.1 ≤ n^2*((n+1)*n*G.card) ∧
      out.2.2 ≤ n*(2*Fintype.card (HeightNode V height)*height*n^2) := by
  obtain ⟨replay,build,template⟩ := prepareEarlyDistanceTableWithTemplateWork_spec G height sample
  refine ⟨?_,build.le.trans (distanceTableWithSearchWork_bound G),template⟩
  simp only [completeSteinerPrefixSearchReplayWithTemplateWork, replay, completeSteinerPrefixSearchReplay]
  rfl

/-- One table and paired template serve all the prefixes. The second field
charges the table's original-graph searches once, outside the prefix list. -/
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
