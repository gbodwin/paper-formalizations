import OnlineReachabilityPreservers.SteinerStackTagging

/-! Stack subroutines retain passive tapes when mounted in a larger tape set. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

namespace StackIndexEmbedding

open StackMachineTag (Program)

variable {K H A L S : Type} (slot : K ↪ H)

/-- Replace each tape index by its position in the host's tape set. -/
def statement : Program K A L S → Program H A L S
  | push k f rest => push (slot k) f (statement rest)
  | peek k f rest => peek (slot k) f (statement rest)
  | pop k f rest => pop (slot k) f (statement rest)
  | load f rest => load f (statement rest)
  | branch f yes no => branch f (statement yes) (statement no)
  | goto f => goto f
  | halt => halt

open scoped Classical in
/-- Use the subroutine's tapes on embedded slots and the supplied host
tapes everywhere else. This describes a configuration in the proof. -/
noncomputable def tapesAt (active : K → List A) (extra : H → List A) (j : H) : List A :=
  if found : ∃ k, slot k = j then active (Classical.choose found) else extra j

@[simp]
theorem tapesAt_image (active : K → List A) (extra : H → List A) (k : K) :
    tapesAt slot active extra (slot k) = active k := by
  have found : ∃ j, slot j = slot k := ⟨k,rfl⟩
  unfold tapesAt
  rw [dite_eq_left found]
  exact congrArg active (slot.injective (Classical.choose_spec found))

theorem tapesAt_extra (active : K → List A) (extra : H → List A) {j : H}
    (outside : ∀ k, slot k ≠ j) : tapesAt slot active extra j = extra j := by
  unfold tapesAt
  exact dite_eq_right fun ⟨k,equal⟩ => outside k equal

/-- Embed the tapes of a configuration while keeping its label and register. -/
noncomputable def configuration (extra : H → List A) (c : Turing.TM2.Cfg (fun _ : K => A) L S) :
    Turing.TM2.Cfg (fun _ : H => A) L S where
  l := c.l
  var := c.var
  stk := tapesAt slot c.stk extra

variable [DecidableEq K] [DecidableEq H]

private theorem update_tapesAt (active : K → List A) (extra : H → List A) (k : K) (word : List A) :
    Function.update (tapesAt slot active extra) (slot k) word =
      tapesAt slot (Function.update active k word) extra := by
  funext j
  by_cases found : ∃ i, slot i = j
  · obtain ⟨i,rfl⟩ := found
    by_cases same : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne (slot.injective.ne same),tapesAt_image,Function.update_of_ne same]
  · have apart : j ≠ slot k := fun same => found ⟨k,same.symm⟩
    have outside (i : K) : slot i ≠ j := fun same => found ⟨i,same⟩
    simp only [Function.update_of_ne apart,tapesAt_extra slot _ _ outside]

/-- Each instruction updates only the active tapes at their embedded indices. -/
theorem stepAux_statement (extra : H → List A) (code : Program K A L S) (r : S) (active : K → List A) :
    Turing.TM2.stepAux (statement slot code) r (tapesAt slot active extra) =
      configuration slot extra (Turing.TM2.stepAux code r active) := by
  induction code generalizing r active with
  | push k f rest ih =>
    simp only [statement,Turing.TM2.stepAux,tapesAt_image,update_tapesAt]
    exact ih _ _
  | peek k f rest ih =>
    simp only [statement,Turing.TM2.stepAux,tapesAt_image]
    exact ih _ _
  | pop k f rest ih =>
    simp only [statement,Turing.TM2.stepAux,tapesAt_image,update_tapesAt]
    exact ih _ _
  | load f rest ih => exact ih _ _
  | branch f yes no left right =>
    cases choice : f r <;> simp [Turing.TM2.stepAux,statement,choice,left,right]
  | goto f => rfl
  | halt => rfl

/-- The host's corresponding transition preserves the additional tapes. -/
theorem step_on {base : L → Program K A L S} (extra : H → List A)
    (c : Turing.TM2.Cfg (fun _ : K => A) L S) :
    Turing.TM2.step (statement slot ∘ base) (configuration slot extra c) =
      (Turing.TM2.step base c).map (configuration slot extra) := by
  rcases c with ⟨label,r,active⟩
  cases label with
  | none => rfl
  | some l =>
    change some (Turing.TM2.stepAux (statement slot (base l)) r (tapesAt slot active extra)) = _
    rw [stepAux_statement]
    rfl

/-- Embed a certified execution on more tapes with the exact same number
of transitions and the supplied passive tapes present throughout. -/
def evaluation {base : L → Program K A L S} (extra : H → List A)
    {c : Turing.TM2.Cfg (fun _ : K => A) L S}
    {answer : Option (Turing.TM2.Cfg (fun _ : K => A) L S)} {bound : ℕ}
    (run : EvalsToInTime (Turing.TM2.step base) c answer bound) :
    EvalsToInTime (Turing.TM2.step (statement slot ∘ base))
      (configuration slot extra c) (answer.map (configuration slot extra)) bound where
  steps := run.steps
  steps_le_m := run.steps_le_m
  evals_in_steps := by
    have commute : Function.Semiconj (Option.map (configuration slot extra))
        (flip bind (Turing.TM2.step base)) (flip bind (Turing.TM2.step (statement slot ∘ base))) := by
      intro prior
      cases prior with
      | none => rfl
      | some old => exact (step_on slot extra old).symm
    have both := (commute.iterate_right run.steps) (some c)
    rw [run.evals_in_steps] at both
    exact both.symm

end StackIndexEmbedding

end OnlineReachabilityPreservers
