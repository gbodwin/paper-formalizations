import LightEFTFairBitStage.FairBitDigitSampler

/-! Unelaborated source. Explicit independent fresh-call OUTPUT semantics;
this is not a refinement proof for a charged one-stream cursor implementation.
Each scalar law below is derived from the actual fair-bit execution tree.
No caller-supplied tensor or uniform Fin (2*f) draw is assumed generated. -/
namespace LightEFTSpanners.FairBitDigit
open Finset FiniteProbability
attribute [local instance] Classical.propDecidable

/-- Independently invoke the derived scalar sampler once per consecutive position.
Law.bind supplies fresh randomness after fixing the previous output. -/
noncomputable def independentCalls (p : Law Bool) : (N : ℕ) → Law (Fin N → Bool)
  | 0 => Law.pure (fun i => Fin.elim0 i)
  | N+1 => p.bind fun b => (independentCalls p N).map (Fin.cons b)

theorem independentCalls_probability (p : Law Bool) (N : ℕ)
    (P : (Fin N → Bool) → Prop) :
    (independentCalls p N).prob P = (productLaw (J:=Fin N) p).prob P := by
  classical
  induction N generalizing P with
  | zero =>
    let empty : Fin 0 → Bool := fun i => Fin.elim0 i
    have he : (fun x : Fin 0 → Bool => P x) = (fun _ => P empty) := by
      funext x
      have hx : x = empty := by funext i; exact Fin.elim0 i
      rw [hx]
    calc
      _ = if P empty then 1 else 0 := by rw [independentCalls, Law.prob_pure]
      _ = (productLaw (J:=Fin 0) p).prob (fun _ => P empty) :=
        (Law.prob_const _ _).symm
      _ = _ := by rw [←he]
  | succ N ih =>
    rw [independentCalls, Law.prob_bind, JointFlagSampling.Transport.fin_cons_probability]
    apply Finset.sum_congr rfl
    intro b _
    rw [Law.prob_map, ih]

theorem independentCalls_eq_product (p : Law Bool) (N : ℕ) :
    independentCalls p N = productLaw (J:=Fin N) p := by
  apply JointFlagSampling.Transport.eq_of_prob_eq
  intro P
  exact independentCalls_probability p N P

noncomputable def samplerLaw (f : ℕ) (hf : 0 < f) : Law Bool :=
  outputLaw (2*f) (by omega) (initial f hf)

theorem samplerLaw_mass (f : ℕ) (hf : 0 < f) (b : Bool) :
    (samplerLaw f hf).mass b =
      if b then 1/(2*(f:ℝ)) else 1-1/(2*(f:ℝ)) := by
  change (if b then fraction (2*f) (initial f hf)
    else 1-fraction (2*f) (initial f hf)) = _
  simp only [initial_fraction]

/-- This scalar output law is derived from fair-bit terminal execution masses. -/
theorem samplerLaw_execution_mass (f : ℕ) (hf : 0 < f) (b : Bool) :
    HasSum (fun t => if outputAt (2*f) (by omega) (initial f hf) t = b
      then terminalWeight t else 0) ((samplerLaw f hf).mass b) := by
  exact outputLaw_execution_mass (2*f) (by omega) (initial f hf) b

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Finite independent-call composition realizes the reviewed ideal vector law.
The implementation-level fresh-tail/cursor refinement is a separate obligation. -/
theorem independentCalls_flat_law (n f m : ℕ) (hf : 0 < f)
    (l : List (JointFlagSampling.OriginalEdge n)) :
    independentCalls (samplerLaw f hf) (FlatTape.tapeLength (J:=J) n m l) =
      FlatTape.idealTapeLaw (J:=J) n f m hf l := by
  rw [independentCalls_eq_product]
  apply JointFlagSampling.Transport.mass_ext
  intro tape
  change (∏ k, (samplerLaw f hf).mass (tape k)) =
    (FlatTape.idealTapeLaw (J:=J) n f m hf l).mass tape
  rw [FlatTape.idealTapeLaw_mass]
  simp only [samplerLaw_mass]

theorem independentCalls_assignment_probability (n f m : ℕ) (hf : 0 < f)
    (l : List (JointFlagSampling.OriginalEdge n))
    (P : SampledGreedy.Assignment (Fin n) J m → Prop) :
    (independentCalls (samplerLaw f hf) (FlatTape.tapeLength (J:=J) n m l)).prob
        (fun tape => P (PaidJointBridge.storedAssignment l
          (FlatTape.tapeEquiv (J:=J) n m l tape))) =
      (SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m l).prob P := by
  rw [independentCalls_flat_law]
  exact FlatTape.tape_supplied_assignment_probability (J:=J) n f m hf l P

end LightEFTSpanners.FairBitDigit
