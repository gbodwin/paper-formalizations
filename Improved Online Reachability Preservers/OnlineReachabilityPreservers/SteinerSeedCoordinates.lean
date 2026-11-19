import OnlineReachabilityPreservers.SteinerComplete

/-! The independent coordinate representation of the early random seed. -/

namespace OnlineReachabilityPreservers

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- A coordinate selects one trial, root, tier, and either its shared
gate or one history test on one side. -/
abbrev EarlySeedCoordinate (G : Arcs V) (height : ℕ) :=
  Fin (earlyTrialCount V height) × V × Fin ((forestScale G height).log2 + 1) ×
    Option (Bool × HeightNode V height)

/-- Flatten the seed into independent grid choices. The grid of size
`2 ^ (scale.log2 + 1)` is a bit vector of length `scale.log2 + 1`. -/
def earlySeedCoordinates (G : Arcs V) (height : ℕ) :
    EarlyRoundSample G height ≃ (EarlySeedCoordinate G height → Fin (forestSeedSize (forestScale G height))) where
  toFun seeds := fun
    | (trial, root, tier, none) => (seeds trial root tier).1
    | (trial, root, tier, some (side, node)) => (seeds trial root tier).2 side node
  invFun values := fun trial root tier =>
    (values (trial, root, tier, none), fun side node => values (trial, root, tier, some (side, node)))
  left_inv seeds := by
    funext trial root tier
    rfl
  right_inv values := by
    funext coordinate
    rcases coordinate with ⟨trial, root, tier, test⟩
    cases test with
    | none => rfl
    | some test =>
      cases test
      rfl

local instance earlyCoordinateAssignmentFintype (G : Arcs V) (height : ℕ) :
    Fintype (EarlySeedCoordinate G height → Fin (forestSeedSize (forestScale G height))) :=
  Fintype.ofEquiv (EarlyRoundSample G height) (earlySeedCoordinates G height)

theorem earlySeedCoordinates_probability (G : Arcs V) (height : ℕ)
    (event : Finset (EarlyRoundSample G height)) :
    finiteProbability (event.map (earlySeedCoordinates G height).toEmbedding) =
      finiteProbability event := by
  simp only [finiteProbability, Finset.card_map,
    Fintype.card_congr (earlySeedCoordinates G height)]

theorem earlySeedCoordinate_card (G : Arcs V) (height : ℕ) :
    Fintype.card (EarlySeedCoordinate G height) =
      earlyTrialCount V height * (Fintype.card V * (((forestScale G height).log2 + 1) *
        (2 * Fintype.card (HeightNode V height) + 1))) := by
  simp only [EarlySeedCoordinate, Fintype.card_prod, Fintype.card_fin, Fintype.card_option, Fintype.card_bool]

theorem earlySeedCoordinate_card_le [Nonempty V] (G : Arcs V) (height : ℕ) :
    Fintype.card (EarlySeedCoordinate G height) ≤
      earlyTrialCount V height * (Fintype.card V * (((forestScale G height).log2 + 1) *
        (2 * ((height + 1) * Fintype.card V ^ height) + 1))) := by
  rw [earlySeedCoordinate_card]
  gcongr
  exact heightNode_card_le V height

theorem completeSteinerHubCount_le (V : Type*) [Fintype V] :
    completeSteinerHubCount V ≤ 4 * ((Fintype.card V).log2 + 1) * Fintype.card V + 1 := by
  unfold completeSteinerHubCount steinerHubDraws
  split
  · exact Nat.zero_le _
  · exact Nat.add_le_add_right (Nat.div_le_self _ _) _

end OnlineReachabilityPreservers
