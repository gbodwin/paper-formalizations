import Mathlib.Computability.TuringMachine.Computable

/-! Embed a stack program with one common alphabet in a machine with tagged symbols and labels. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing Turing.TM2.Stmt

/-- Symbol, register and label maps for a tagged subroutine. The reads
recover the original symbols and register on embedded configurations. -/
structure StackMachineTag (A B L M S T : Type) where
  writeSymbol : A → B
  readSymbol : B → Option A
  writeRegister : S → T
  readRegister : T → S
  writeLabel : L → M
  read_written_symbol : ∀ a, readSymbol (writeSymbol a) = some a
  read_written_register : ∀ r, readRegister (writeRegister r) = r

namespace StackMachineTag

variable {K A B L M S T : Type} (tag : StackMachineTag A B L M S T)

/-- Instructions with a common symbol alphabet across all tape stacks. -/
abbrev Program (K A L S : Type) := Turing.TM2.Stmt (fun _ : K => A) L S

/-- Relabel every instruction of a program that uses the same alphabet on each stack. -/
def statement : Program K A L S → Program K B M T
  | push k f rest => push k (fun r => tag.writeSymbol (f (tag.readRegister r))) (statement rest)
  | peek k f rest =>
      peek k (fun r a => tag.writeRegister (f (tag.readRegister r) (a.bind tag.readSymbol))) (statement rest)
  | pop k f rest =>
      pop k (fun r a => tag.writeRegister (f (tag.readRegister r) (a.bind tag.readSymbol))) (statement rest)
  | load f rest => load (fun r => tag.writeRegister (f (tag.readRegister r))) (statement rest)
  | branch f yes no => branch (fun r => f (tag.readRegister r)) (statement yes) (statement no)
  | goto f => goto fun r => tag.writeLabel (f (tag.readRegister r))
  | halt => halt

/-- Embed the register, stack words, and optional control label. -/
def configuration (c : Turing.TM2.Cfg (fun _ : K => A) L S) :
    Turing.TM2.Cfg (fun _ : K => B) M T where
  l := c.l.map tag.writeLabel
  var := tag.writeRegister c.var
  stk k := (c.stk k).map tag.writeSymbol

variable [DecidableEq K]

private theorem map_update (tapes : K → List A) (k : K) (values : List A) :
    Function.update (fun j => (tapes j).map tag.writeSymbol) k (values.map tag.writeSymbol) =
      fun j => ((Function.update tapes k values) j).map tag.writeSymbol := by
  funext j
  by_cases same : j = k
  · subst j
    simp
  · simp [Function.update_of_ne same]

private theorem mapped_head (values : List A) :
    (values.map tag.writeSymbol).head?.bind tag.readSymbol = values.head? := by
  cases values <;> simp [tag.read_written_symbol]

private theorem mapped_tail (values : List A) :
    (values.map tag.writeSymbol).tail = values.tail.map tag.writeSymbol := by
  cases values <;> rfl

/-- Tagging a statement preserves its transition on an embedded state and tapes. -/
theorem stepAux_statement (code : Program K A L S) (r : S) (tapes : K → List A) :
    Turing.TM2.stepAux (tag.statement code) (tag.writeRegister r) (fun k => (tapes k).map tag.writeSymbol) =
      tag.configuration (Turing.TM2.stepAux code r tapes) := by
  induction code generalizing r tapes with
  | push k f rest ih =>
    simp only [statement,Turing.TM2.stepAux,tag.read_written_register,← List.map_cons,tag.map_update]
    exact ih r _
  | peek k f rest ih =>
    simp only [statement,Turing.TM2.stepAux,tag.read_written_register,tag.mapped_head]
    exact ih _ tapes
  | pop k f rest ih =>
    simp only [statement,Turing.TM2.stepAux,tag.read_written_register,tag.mapped_head,tag.mapped_tail,tag.map_update]
    exact ih _ _
  | load f rest ih =>
    simp only [statement,Turing.TM2.stepAux,tag.read_written_register]
    exact ih _ tapes
  | branch f yes no ihYes ihNo =>
    cases choose : f r <;>
      simp [statement,Turing.TM2.stepAux,tag.read_written_register,choose,ihYes,ihNo]
  | goto f => simp [statement,Turing.TM2.stepAux,tag.read_written_register,configuration]
  | halt => rfl

/-- A host program can supply arbitrary other labels. At an embedded
label it executes the corresponding subroutine transition. -/
theorem step_embedded {base : L → Program K A L S} {host : M → Program K B M T}
    (on : ∀ l, host (tag.writeLabel l) = tag.statement (base l))
    (c : Turing.TM2.Cfg (fun _ : K => A) L S) :
    Turing.TM2.step host (tag.configuration c) = (Turing.TM2.step base c).map tag.configuration := by
  rcases c with ⟨label,r,tapes⟩
  cases label with
  | none => rfl
  | some l =>
    change some (Turing.TM2.stepAux (host (tag.writeLabel l)) (tag.writeRegister r) _) =
      some (tag.configuration (Turing.TM2.stepAux (base l) r tapes))
    rw [on,tag.stepAux_statement]

/-- The embedding preserves any certified subroutine evaluation and its transition count. -/
def evaluation {base : L → Program K A L S} {host : M → Program K B M T}
    (on : ∀ l, host (tag.writeLabel l) = tag.statement (base l))
    {c : Turing.TM2.Cfg (fun _ : K => A) L S}
    {answer : Option (Turing.TM2.Cfg (fun _ : K => A) L S)} {bound : ℕ}
    (run : EvalsToInTime (Turing.TM2.step base) c answer bound) :
    EvalsToInTime (Turing.TM2.step host) (tag.configuration c) (answer.map tag.configuration) bound where
  steps := run.steps
  steps_le_m := run.steps_le_m
  evals_in_steps := by
    have commute : Function.Semiconj (Option.map tag.configuration)
        (flip bind (Turing.TM2.step base)) (flip bind (Turing.TM2.step host)) := by
      intro prior
      cases prior with
      | none => rfl
      | some old => exact (tag.step_embedded on old).symm
    have both := (commute.iterate_right run.steps) (some c)
    rw [run.evals_in_steps] at both
    exact both.symm

end StackMachineTag

end OnlineReachabilityPreservers
