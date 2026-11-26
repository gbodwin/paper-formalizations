import OnlineReachabilityPreservers.SteinerBinaryReplaySizeWork

/-! Transfer the fixed-budget competitive guarantee to the binary replay. -/

namespace OnlineReachabilityPreservers

/-- The final graph stored by the replay using both binary solvers. -/
def finSteinerBinaryFinalGraph {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) : Arcs (Fin n) :=
  let out := completeFinSteinerReplayWithBinaryPhasesWork G raw same height G.card rfl bits D
  (out.1.1.1.1.1.getLastD (∅,0)).1

private theorem getLast_inits {A : Type*} (D : List A) : D.inits.getLast? = some D := by
  rw [List.inits_eq_tails,List.getLast?_reverse,List.head?_map]
  have first (P : List A) : P.tails.head? = some P := by
    cases P <;> rfl
  rw [first,Option.map_some,List.reverse_reverse]

/-- The executable's last record is the fixed-budget reference run on the
whole trace, including when the given seed is exhausted. -/
theorem finSteinerBinaryFinalGraph_eq {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    finSteinerBinaryFinalGraph G raw same height bits D = completeSteinerRunWithBitBudget G height bits D := by
  let out := completeFinSteinerReplayWithBinaryPhasesWork G raw same height G.card rfl bits D
  let records := out.1.1.1.1.1
  have graphs : records.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) :=
    (completeFinSteinerReplayWithBinaryPhasesWork_prefixes G raw same height G.card rfl bits D feasible).1
  change (records.getLastD (∅,0)).1 = _
  rw [← List.getLastD_map (f := Prod.fst),graphs,List.getLastD_eq_getLast?,List.getLast?_map,getLast_inits]
  rfl

/-- For every seed, the binary replay returns a subgraph serving every
request of the feasible trace. -/
theorem finSteinerBinaryFinalGraph_correct {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let graph := finSteinerBinaryFinalGraph G raw same height bits D
    graph ⊆ G ∧ Preserves G graph D := by
  rw [finSteinerBinaryFinalGraph_eq G raw same height bits D feasible]
  exact completeSteinerRunWithBitBudget_correct G height bits D feasible

/-- The binary replay is irrevocable on feasible traces with the same
input graph and seed. -/
theorem finSteinerBinaryFinalGraph_prefix {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    {D E : List (Fin n × Fin n)} (prefixOf : D <+: E) (feasible : ∀ d ∈ E, Reach G d.1 d.2) :
    finSteinerBinaryFinalGraph G raw same height bits D ⊆ finSteinerBinaryFinalGraph G raw same height bits E := by
  rw [finSteinerBinaryFinalGraph_eq G raw same height bits D (fun d h => feasible d (prefixOf.subset h)),
    finSteinerBinaryFinalGraph_eq G raw same height bits E feasible]
  exact completeSteinerRunWithBitBudget_prefix G height bits prefixOf feasible

/-- Theorem 21's expected edge bound for the graph computed with both
binary solvers, under the uniform finite seed law on each fixed trace. -/
theorem theorem21_online_steiner_binary_replay_expected {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ {n : ℕ} {G Z : Arcs (Fin n)} (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (D : List (Fin n × Fin n)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∑ bits : Fin (steinerBitBudget G height) → Bool,
          ((finSteinerBinaryFinalGraph G raw same height bits D).card : ℝ)) /
          (Fintype.card (Fin (steinerBitBudget G height) → Bool) : ℝ) ≤ K * (n : ℝ) ^ (3/5 + ε) * Z.card := by
  obtain ⟨height,heightPos,K,Kpos,expected⟩ := theorem21_online_steiner_bounded_bits_finite epsilon
  refine ⟨height,heightPos,K,Kpos,?_⟩
  intro n G Z raw same D sub demands
  have feasible (d : Fin n × Fin n) (inside : d ∈ D) : Reach G d.1 d.2 := reach_mono sub (demands d inside)
  simp_rw [fun bits => finSteinerBinaryFinalGraph_eq G raw same height bits D feasible]
  simpa only [Fintype.card_fin] using expected (Fin n) D sub demands

end OnlineReachabilityPreservers
