import LightEFTSpanners.CorrectedRuntimeWork
import LightEFTSpanners.CorrectedRuntimeGeneralWork
import LightEFTSpanners.CorrectedVotingOutput
import LightEFTSpanners.FiniteLaw
import LightEFTSpanners.ConnectivityOptimum

/-! Exact output bridge for the corrected rational program. The graph seed,
host family, sorted edge list and sample assignments are supplied inputs;
the executable recursion does not choose them or generate randomness. -/
namespace LightEFTSpanners.CorrectedRuntime
open SimpleGraph Finset LightSpanners

variable {n : ℕ} {J : Type*} [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- Rational stretch, so executable distance tests use exact arithmetic. -/
def paperStretch (eps : ℚ) (k : ℕ) : ℚ := (1+eps)*(2*k-1)

@[simp] theorem paperStretch_cast (eps : ℚ) (k : ℕ) :
    (paperStretch eps k : ℝ) = (1+(eps:ℝ))*(2*k-1) := by
  simp [paperStretch]

/-- Output of the literal rational recursion on the supplied, mathematically
specified sorted input. Preparing that input is outside this function's cost. -/
noncomputable def output (G Q : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e, 0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) J)
    (h : ℕ) : SimpleGraph (Fin n) :=
  edgeGraph (edges Q.edgeFinset w hw t eligible host tape h
    (input G Q (fun e => (w e:ℝ))))

omit [DecidableEq J] in
theorem output_eq (G Q : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e, 0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : CorrectedVoting.Tape (Fin n) J)
    (h : ℕ) :
    output G Q w hw t eligible host tape h =
      CorrectedVoting.output G Q (fun e => (w e:ℝ)) (t:ℝ) eligible host tape h := by
  unfold output CorrectedVoting.output
  rw [edges_eq]

/-- A concrete finite host-indexed implementation returns the corrected
mathematical graph and has the stated paid loop bound. No accuracy premise is
needed for either execution equality or its cost. -/
theorem measured_output_spec {j : ℕ} (G Q : SimpleGraph (Fin n))
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e, 0≤w e) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset (Fin j))
    (host : Fin j → Finset (Sym2 (Fin n))) (m : ℕ)
    (a : CorrectedVoting.Assignment (Fin n) (Fin j) m) (h : ℕ) :
    edgeGraph (edgesWork Q.edgeFinset w hw t eligible host
      (CorrectedVoting.assignmentTape a) h (input G Q (fun e => (w e:ℝ)))).1 =
      CorrectedVoting.output G Q (fun e => (w e:ℝ)) (t:ℝ) eligible host
        (CorrectedVoting.assignmentTape a) h ∧
    (edgesWork Q.edgeFinset w hw t eligible host
      (CorrectedVoting.assignmentTape a) h (input G Q (fun e => (w e:ℝ)))).2 ≤
      1+(input G Q (fun e => (w e:ℝ))).length*
        (j*(m*(distanceBudget n+2)+5)+4) := by
  obtain ⟨he,hcost⟩ := assignment_run_spec Q.edgeFinset w hw t eligible host m a h
    (input G Q (fun e => (w e:ℝ)))
  exact ⟨congrArg edgeGraph he,hcost⟩

/-- Arbitrary finite host identities are handled using a complete supplied
enumeration, rather than an uncharged enumeration primitive. -/
theorem enumerated_output_spec [Fintype J] (hostIndices : List J)
    (hIndices : hostIndices.toFinset = (univ : Finset J))
    (G Q : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e, 0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (m : ℕ)
    (a : CorrectedVoting.Assignment (Fin n) J m) (h : ℕ) :
    edgeGraph (CorrectedExecution.edgesWork hostIndices Q.edgeFinset w hw t eligible host
      (CorrectedVoting.assignmentTape a) h (input G Q (fun e => (w e:ℝ)))).1 =
      CorrectedVoting.output G Q (fun e => (w e:ℝ)) (t:ℝ) eligible host
        (CorrectedVoting.assignmentTape a) h ∧
    (CorrectedExecution.edgesWork hostIndices Q.edgeFinset w hw t eligible host
      (CorrectedVoting.assignmentTape a) h (input G Q (fun e => (w e:ℝ)))).2 ≤
      1+(input G Q (fun e => (w e:ℝ))).length*
        (hostIndices.length*(m*(distanceBudget n+2)+5)+4) := by
  obtain ⟨he,hcost⟩ := CorrectedExecution.assignment_run_spec hostIndices Q.edgeFinset
    w hw t eligible host m a h (input G Q (fun e => (w e:ℝ))) hIndices
  exact ⟨congrArg edgeGraph he,hcost⟩

/-- The instrumented program's combined correctness, lightness and cost
failure event is contained in the proved mathematical failure event, for
every law on the supplied assignments. The cost holds for every assignment. -/
theorem measured_failure_probability_le [Fintype J] (hostIndices : List J)
    (hIndices : hostIndices.toFinset = (univ : Finset J))
    (G Q R : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e, 0≤w e) (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (m f h : ℕ) (B : ℝ)
    (law : FiniteProbability.Law (CorrectedVoting.Assignment (Fin n) J m)) :
    law.prob (fun a =>
      let result := CorrectedExecution.edgesWork hostIndices Q.edgeFinset w hw t eligible host
        (CorrectedVoting.assignmentTape a) h (input G Q (fun e => (w e:ℝ)))
      ¬(IsEFTSpanner G (edgeGraph result.1) (fun e => (w e:ℝ)) (t:ℝ) f ∧
        competitiveLightness (edgeGraph result.1) R (fun e => (w e:ℝ)) ≤ B ∧
        result.2 ≤ 1+(input G Q (fun e => (w e:ℝ))).length*
          (hostIndices.length*(m*(distanceBudget n+2)+5)+4))) ≤
    law.prob (fun a => ¬(
      IsEFTSpanner G (CorrectedVoting.output G Q (fun e => (w e:ℝ)) (t:ℝ)
        eligible host (CorrectedVoting.assignmentTape a) h) (fun e => (w e:ℝ)) (t:ℝ) f ∧
      competitiveLightness (CorrectedVoting.output G Q (fun e => (w e:ℝ)) (t:ℝ)
        eligible host (CorrectedVoting.assignmentTape a) h) R (fun e => (w e:ℝ)) ≤ B)) := by
  apply FiniteProbability.Law.prob_mono
  intro a hbad hgood
  apply hbad
  obtain ⟨he,hcost⟩ := enumerated_output_spec hostIndices hIndices G Q w hw t eligible host m a h
  exact ⟨by simpa only [he] using hgood.1,
    by simpa only [he] using hgood.2,hcost⟩

end LightEFTSpanners.CorrectedRuntime
