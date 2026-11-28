import OnlineReachabilityPreservers.SteinerStackTagging

/-! Timed simulations of subroutines that return control to a host program. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

private def redirectHalt {K L S : Type} {Γ : K → Type} (ret : L) :
    Turing.TM2.Stmt Γ L S → Turing.TM2.Stmt Γ L S
  | push k f rest => push k f (redirectHalt ret rest)
  | peek k f rest => peek k f (redirectHalt ret rest)
  | pop k f rest => pop k f (redirectHalt ret rest)
  | load f rest => load f (redirectHalt ret rest)
  | branch f yes no => branch f (redirectHalt ret yes) (redirectHalt ret no)
  | goto f => goto f
  | halt => goto fun _ => ret

private def redirectCfg {K L S : Type} {Γ : K → Type} (ret : L) (c : Turing.TM2.Cfg Γ L S) :
    Turing.TM2.Cfg Γ L S :=
  {c with l := some (c.l.getD ret)}

private theorem stepAux_redirect {K L S : Type} {Γ : K → Type} [DecidableEq K]
    (ret : L) (code : Turing.TM2.Stmt Γ L S) (r : S) (tapes : ∀ k, List (Γ k)) :
    Turing.TM2.stepAux (redirectHalt ret code) r tapes =
      redirectCfg ret (Turing.TM2.stepAux code r tapes) := by
  induction code generalizing r tapes with
  | push k f rest ih => exact ih _ _
  | peek k f rest ih => exact ih _ _
  | pop k f rest ih => exact ih _ _
  | load f rest ih => exact ih _ _
  | branch f yes no left right =>
    cases choice : f r <;> simp [Turing.TM2.stepAux,redirectHalt,choice,left,right]
  | goto f => rfl
  | halt => rfl

private theorem iterate_map_some {S T : Type} (map : S → T) {base : S → Option S}
    {host : T → Option T} (move : ∀ {a b}, base a = some b → host (map a) = some (map b))
    (steps : ℕ) {a b : S} (run : (flip bind base)^[steps] (some a) = some b) :
    (flip bind host)^[steps] (some (map a)) = some (map b) := by
  induction steps generalizing a with
  | zero =>
    have equal : a = b := Option.some.inj run
    subst b
    rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply] at run ⊢
    change (flip bind base)^[steps] (base a) = some b at run
    change (flip bind host)^[steps] (host (map a)) = some (map b)
    cases first : base a with
    | none =>
      have stays : (flip bind base)^[steps] (none : Option S) = none :=
        Function.iterate_fixed (f := flip bind base) rfl steps
      rw [first,stays] at run
      contradiction
    | some next =>
      rw [move first]
      exact ih (by simpa only [first] using run)

namespace StackMachineTag

variable {K A B L M S T : Type} (tag : StackMachineTag A B L M S T)

/-- Embed a subroutine statement and redirect its halt to a host label. -/
def returningStatement (ret : M) (code : Program K A L S) : Program K B M T :=
  redirectHalt ret (tag.statement code)

/-- An embedded subroutine's halt is a live return label for the host. -/
def returningConfiguration (ret : M) (c : Turing.TM2.Cfg (fun _ : K => A) L S) :
    Turing.TM2.Cfg (fun _ : K => B) M T :=
  redirectCfg ret (tag.configuration c)

theorem returningConfiguration_label_of_halt (ret : M) (c : Turing.TM2.Cfg (fun _ : K => A) L S)
    (halted : c.l = none) : (tag.returningConfiguration ret c).l = some ret := by
  simp [returningConfiguration,redirectCfg,configuration,halted]

variable [DecidableEq K]

/-- Each successful subroutine step becomes exactly one host step,
including the step that would halt the subroutine. -/
theorem step_embedded_return (ret : M) {base : L → Program K A L S} {host : M → Program K B M T}
    (on : ∀ l, host (tag.writeLabel l) = tag.returningStatement ret (base l))
    {c after : Turing.TM2.Cfg (fun _ : K => A) L S}
    (move : Turing.TM2.step base c = some after) :
    Turing.TM2.step host (tag.returningConfiguration ret c) =
      some (tag.returningConfiguration ret after) := by
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => contradiction
  | some l =>
    have afterStep : Turing.TM2.stepAux (base l) r tapes = after := Option.some.inj move
    rw [← afterStep]
    change some (Turing.TM2.stepAux (host (tag.writeLabel l))
      (tag.writeRegister r) (fun k => (tapes k).map tag.writeSymbol)) = _
    rw [on]
    unfold returningStatement
    rw [stepAux_redirect,tag.stepAux_statement]
    rfl

/-- A terminating subroutine evaluation lands at the live host return
point with its exact result and original number of steps. -/
def evaluationReturning (ret : M) {base : L → Program K A L S} {host : M → Program K B M T}
    (on : ∀ l, host (tag.writeLabel l) = tag.returningStatement ret (base l))
    {c answer : Turing.TM2.Cfg (fun _ : K => A) L S} {bound : ℕ}
    (run : EvalsToInTime (Turing.TM2.step base) c (some answer) bound) :
    EvalsToInTime (Turing.TM2.step host) (tag.returningConfiguration ret c)
      (some (tag.returningConfiguration ret answer)) bound where
  steps := run.steps
  steps_le_m := run.steps_le_m
  evals_in_steps := iterate_map_some (tag.returningConfiguration ret)
    (fun move => tag.step_embedded_return ret on move) run.steps run.evals_in_steps

end StackMachineTag

end OnlineReachabilityPreservers
