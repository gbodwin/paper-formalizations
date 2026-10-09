import DirectedFlowCutGap.MinimumClosureCut
import DirectedFlowCutGap.IntegralMaxFlow

/-!
# Closure optimization by a computed augmentation budget

The actual integral-flow recursion runs for `sum |cost|` steps. A feasible
closure is used only in the proof of the bound and is not inspected by the
recursion. Any certified residual-path search can instantiate the procedure.
The supplied classical search and reachability extraction certify existence;
efficient graph search and operation counts remain separate obligations.
-/
namespace DirectedFlowCutGap.MinimumClosureOptimizer

noncomputable section
open MinimumClosureProblem MinimumClosureCut IntegralNetworkFlow

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The number of recursion steps is computed directly from the integer costs. -/
def runFlow (P : Problem A) (find : PathSearch (capacity P) source sink) :
    Flow (capacity P) source sink :=
  run find (Flow.zero (capacity P) source sink) (budget P)

/-- Any feasible closure bounds every augmentation, so the computed budget
suffices without computing that witness closure's cut capacity. -/
theorem runFlow_no_path (P : Problem A) (find : PathSearch (capacity P) source sink)
    (T₀ : Finset A) (hT₀ : P.IsClosed T₀) :
    ¬Nonempty (SimplePath (runFlow P find).residual source sink) := by
  intro hp
  have hst : (source : MinimumClosureCut.Vertex A) ≠ sink := by simp [source, sink]
  have hv : (runFlow P find).value = (budget P : ℤ) := by
    simpa [runFlow, Flow.zero_value] using
      run_value_of_path find (Flow.zero (capacity P) source sink) hst (budget P) hp
  obtain ⟨p⟩ := hp
  have hb := flow_value_le_budget P T₀ hT₀ ((runFlow P find).augment p)
  rw [Flow.augment_value _ p hst, hv] at hb
  omega

theorem runFlow_no_walk (P : Problem A) (find : PathSearch (capacity P) source sink)
    (T₀ : Finset A) (hT₀ : P.IsClosed T₀) :
    ¬Nonempty (DirectedWalk (runFlow P find).residual source sink) := by
  intro h
  exact runFlow_no_path P find T₀ hT₀ (nonempty_simplePath_iff_directedWalk.mpr h)

/-- The flow actually produced by the bounded recursion has an exact optimal
cut certificate. Search correctness is explicit; its operation cost is not
assumed or hidden in this theorem. -/
theorem runFlow_certificate (P : Problem A) (find : PathSearch (capacity P) source sink)
    (T₀ : Finset A) (hT₀ : P.IsClosed T₀) :
    source ∈ residualReachable (runFlow P find) ∧
    sink ∉ residualReachable (runFlow P find) ∧
    (runFlow P find).value = (cutCapacity (capacity P) (residualReachable (runFlow P find)) : ℤ) ∧
    (∀ g : Flow (capacity P) source sink, g.value ≤ (runFlow P find).value) ∧
    (∀ Y, source ∈ Y → sink ∉ Y →
      cutCapacity (capacity P) (residualReachable (runFlow P find)) ≤ cutCapacity (capacity P) Y) :=
  certificate_of_no_augmenting_walk (runFlow P find) (runFlow_no_walk P find T₀ hT₀)

/-- The classical residual-reachability set is kept explicit until its finite
search implementation is supplied. -/
def output (P : Problem A) (find : PathSearch (capacity P) source sink) : Finset A :=
  cores (residualReachable (runFlow P find))

/-- The output of the actual bounded recursion attains the signed closure
minimum. No min-cut or minimum-closure optimizer is an input premise. -/
theorem output_optimal (P : Problem A) (find : PathSearch (capacity P) source sink)
    (T₀ : Finset A) (hT₀ : P.IsClosed T₀) :
    P.IsClosed (output P find) ∧ ∀ T, P.IsClosed T → P.objective (output P find) ≤ P.objective T := by
  have hc := runFlow_certificate P find T₀ hT₀
  exact closure_of_minimum_cut P T₀ hT₀ _ hc.1 hc.2.1 hc.2.2.2.2

/-- Existence is obtained from the explicit classical path-search instance.
This statement deliberately makes no polynomial-time claim. -/
theorem exists_optimal (P : Problem A) (T₀ : Finset A) (hT₀ : P.IsClosed T₀) :
    ∃ T, P.IsClosed T ∧ ∀ U, P.IsClosed U → P.objective T ≤ P.objective U := by
  exact ⟨output P (classicalSearch (capacity P) source sink),
    output_optimal P (classicalSearch (capacity P) source sink) T₀ hT₀⟩

end
end DirectedFlowCutGap.MinimumClosureOptimizer
