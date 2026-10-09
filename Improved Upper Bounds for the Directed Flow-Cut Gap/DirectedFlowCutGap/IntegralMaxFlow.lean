import DirectedFlowCutGap.IntegralAugmentation

/-!
# Bounded integral augmentation

Any certified residual-path search can be used by the actual recursion below.
After a number of iterations bounded by a known separating cut capacity, the
constructed flow has no augmenting walk and yields an optimal cut. An explicit
classical search is supplied for existence. Polynomial-time search and operation
counts are separate obligations; a search contract alone is not that runtime proof.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {c : Capacity V} {s t : V}

/-- A search result carries either an actual path or a genuine no-path certificate. -/
inductive PathSearchResult (f : Flow c s t) : Type _
  | found (path : SimplePath f.residual s t)
  | stopped (noPath : ¬Nonempty (SimplePath f.residual s t))

abbrev PathSearch (c : Capacity V) (s t : V) :=
  (f : Flow c s t) → PathSearchResult f

/-- This total finite-path choice certifies existence only; the runtime
implementation will instantiate the same interface with bounded graph search. -/
def classicalSearch (c : Capacity V) (s t : V) : PathSearch c s t := fun f =>
  if h : Nonempty (SimplePath f.residual s t) then
    .found (Classical.choice h) else .stopped h

def Flow.step (find : PathSearch c s t) (f : Flow c s t) : Flow c s t :=
  match find f with
  | .found p => f.augment p
  | .stopped _ => f

theorem Flow.step_eq_self_of_stopped (find : PathSearch c s t) (f : Flow c s t)
    (h : ¬Nonempty (SimplePath f.residual s t)) : f.step find = f := by
  unfold step
  cases find f with
  | found p => exact (h ⟨p⟩).elim
  | stopped _ => rfl

theorem Flow.step_value_of_path (find : PathSearch c s t) (f : Flow c s t)
    (hst : s ≠ t) (h : Nonempty (SimplePath f.residual s t)) :
    (f.step find).value = f.value + 1 := by
  unfold step
  cases find f with
  | found p => exact f.augment_value p hst
  | stopped hn => exact (hn h).elim

theorem Flow.path_of_step_path (find : PathSearch c s t) (f : Flow c s t)
    (h : Nonempty (SimplePath (f.step find).residual s t)) :
    Nonempty (SimplePath f.residual s t) := by
  by_contra hn
  rw [f.step_eq_self_of_stopped find hn] at h
  exact hn h

/-- Every stage stores an actual feasible integral flow. -/
def run (find : PathSearch c s t) (initial : Flow c s t) : ℕ → Flow c s t
  | 0 => initial
  | k + 1 => (run find initial k).step find

@[simp] theorem run_zero (find : PathSearch c s t) (initial : Flow c s t) :
    run find initial 0 = initial := rfl

@[simp] theorem run_succ (find : PathSearch c s t) (initial : Flow c s t) (k : ℕ) :
    run find initial (k+1) = (run find initial k).step find := rfl

/-- If the process is still active, every preceding step increased value. -/
theorem run_value_of_path (find : PathSearch c s t) (initial : Flow c s t)
    (hst : s ≠ t) (k : ℕ)
    (h : Nonempty (SimplePath (run find initial k).residual s t)) :
    (run find initial k).value = initial.value + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := (run find initial k).path_of_step_path find h
      rw [run_succ, (run find initial k).step_value_of_path find hst hp, ih hp]
      push_cast
      ring

/-- Weak duality bounds all augmentations by a concrete known cut, even when
raw source capacity includes large barrier arcs. -/
theorem run_stopped_at_cut_budget (find : PathSearch c s t) (X : Finset V)
    (hs : s ∈ X) (ht : t ∉ X) :
    ¬Nonempty (SimplePath (run find (Flow.zero c s t) (cutCapacity c X)).residual s t) := by
  intro hp
  have hst : s ≠ t := by intro h; exact ht (h ▸ hs)
  have hv := run_value_of_path find (Flow.zero c s t) hst (cutCapacity c X) hp
  obtain ⟨p⟩ := hp
  have hb := weak_duality
    ((run find (Flow.zero c s t) (cutCapacity c X)).augment p) X hs ht
  rw [Flow.augment_value _ p hst, hv, Flow.zero_value] at hb
  omega

/-- The bounded recursion constructs an exact maximum-flow/minimum-cut pair.
This theorem counts augmentations, without asserting that the chosen search
implementation takes polynomial time. -/
theorem run_certificate (find : PathSearch c s t) (X : Finset V)
    (hs : s ∈ X) (ht : t ∉ X) :
    let f := run find (Flow.zero c s t) (cutCapacity c X)
    s ∈ residualReachable f ∧ t ∉ residualReachable f ∧
      f.value = (cutCapacity c (residualReachable f) : ℤ) ∧
      (∀ g : Flow c s t, g.value ≤ f.value) ∧
      (∀ Y : Finset V, s ∈ Y → t ∉ Y →
        cutCapacity c (residualReachable f) ≤ cutCapacity c Y) := by
  let f := run find (Flow.zero c s t) (cutCapacity c X)
  have hn : ¬Nonempty (DirectedWalk f.residual s t) := by
    rintro ⟨q⟩
    obtain ⟨p, _⟩ := q.exists_simplePath
    exact run_stopped_at_cut_budget find X hs ht ⟨p⟩
  exact certificate_of_no_augmenting_walk f hn

end
end DirectedFlowCutGap.IntegralNetworkFlow
