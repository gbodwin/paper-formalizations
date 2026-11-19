import DirectedFlowCutGap.ImmutableReferenceSimulation

/-! A bounded replay of natural-reference instructions for straight-line portions of proofs. -/

namespace DirectedFlowCutGap.ReferenceProgramSteps

open ImmutableReferenceSimulation

def run {C : ℕ} (program : Program C) : ℕ → NaturalState C → Option (NaturalState C × List Event)
  | 0,state => some (state,[])
  | k+1,state => (tickNatural program state).bind fun step =>
    (run program k step.state).map fun tail => (tail.1,step.events++tail.2)

theorem sound {C k : ℕ} {program : Program C} {initial final : NaturalState C} {events : List Event}
    (done : run program k initial=some (final,events)) : NaturalRun program k initial events final := by
  induction k generalizing initial final events with
  | zero =>
    simp only [run,Option.some.injEq,Prod.mk.injEq] at done
    rcases done with ⟨rfl,rfl⟩
    exact .done _
  | succ k ih =>
    simp only [run] at done
    cases step : tickNatural program initial with
    | none => simp [step] at done
    | some next =>
      simp only [step,Option.bind_some] at done
      cases tail : run program k next.state with
      | none => simp [tail] at done
      | some result =>
        rcases result with ⟨out,emitted⟩
        simp only [tail,Option.map_some,Option.some.injEq,Prod.mk.injEq] at done
        rcases done with ⟨rfl,rfl⟩
        exact .step step (ih tail)

end DirectedFlowCutGap.ReferenceProgramSteps
