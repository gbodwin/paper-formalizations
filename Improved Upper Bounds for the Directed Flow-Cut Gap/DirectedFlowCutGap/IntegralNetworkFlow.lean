import DirectedFlowCutGap.EdgeModel

/-!
# Integral directed capacity networks

An antisymmetric integer flow model for the constructive closure optimizer.
Capacities are nonnegative integers. The reverse residual capacity is represented
by the lower bound implied by antisymmetry. This module concerns actual flows,
cuts and residual reachability; it does not assume a max-flow oracle or assert
an implementation running time.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Integer capacities on every ordered pair; zero encodes an absent arc. -/
abbrev Capacity (V : Type*) := V → V → ℕ

/-- A genuine feasible integral flow. Only source and sink may have imbalance. -/
structure Flow (c : Capacity V) (s t : V) where
  amount : V → V → ℤ
  antisymm : ∀ u v, amount u v = -amount v u
  upper : ∀ u v, amount u v ≤ (c u v : ℤ)
  conserve : ∀ v, v ≠ s → v ≠ t → ∑ u, amount v u = 0

namespace Flow
variable {c : Capacity V} {s t : V}

def divergence (f : Flow c s t) (v : V) : ℤ := ∑ u, f.amount v u

def value (f : Flow c s t) : ℤ := f.divergence s

/-- The zero flow starts the integral augmentation process. -/
def zero (c : Capacity V) (s t : V) : Flow c s t where
  amount := fun _ _ => 0
  antisymm := by simp
  upper := by intro u v; exact_mod_cast Nat.zero_le (c u v)
  conserve := by simp

omit [DecidableEq V] in
@[simp] theorem zero_value (c : Capacity V) (s t : V) : (zero c s t).value = 0 := by
  simp [value, divergence, zero]

omit [DecidableEq V] in
theorem self_eq_zero (f : Flow c s t) (v : V) : f.amount v v = 0 := by
  have h := f.antisymm v v
  omega

omit [DecidableEq V] in
theorem lower (f : Flow c s t) (u v : V) : -(c v u : ℤ) ≤ f.amount u v := by
  rw [f.antisymm]
  exact neg_le_neg (f.upper v u)

omit [DecidableEq V] in
/-- The value cannot exceed the actual total outgoing source capacity. -/
theorem value_le_source_capacity (f : Flow c s t) :
    f.value ≤ (∑ v, c s v : ℕ) := by
  change (∑ v, f.amount s v) ≤ _
  push_cast
  exact Finset.sum_le_sum fun v _ => f.upper s v

omit [DecidableEq V] in
/-- All internal contributions cancel, including antiparallel edges. -/
theorem internal_sum_eq_zero (f : Flow c s t) (X : Finset V) :
    (∑ u ∈ X, ∑ v ∈ X, f.amount u v) = 0 := by
  have h : (∑ u ∈ X, ∑ v ∈ X, f.amount u v) =
      -(∑ u ∈ X, ∑ v ∈ X, f.amount u v) := by
    calc
      _ = ∑ v ∈ X, ∑ u ∈ X, f.amount u v := Finset.sum_comm
      _ = ∑ v ∈ X, ∑ u ∈ X, -f.amount v u := by
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro u hu
        exact f.antisymm u v
      _ = _ := by simp
  omega

/-- Net flow leaving an actual vertex cut. -/
def cutFlux (f : Flow c s t) (X : Finset V) : ℤ :=
  ∑ u ∈ X, ∑ v ∈ Xᶜ, f.amount u v

theorem divergence_sum_eq_flux (f : Flow c s t) (X : Finset V) :
    (∑ u ∈ X, f.divergence u) = f.cutFlux X := by
  have hsplit : (∑ u ∈ X, f.divergence u) =
      (∑ u ∈ X, ∑ v ∈ X, f.amount u v) + f.cutFlux X := by
    rw [cutFlux, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    exact (Finset.sum_add_sum_compl X (fun v => f.amount u v)).symm
  rw [f.internal_sum_eq_zero, zero_add] at hsplit
  exact hsplit

theorem cutFlux_eq_value (f : Flow c s t) (X : Finset V)
    (hs : s ∈ X) (ht : t ∉ X) : f.cutFlux X = f.value := by
  rw [← f.divergence_sum_eq_flux]
  change (∑ u ∈ X, f.divergence u) = f.divergence s
  apply Finset.sum_eq_single s
  · intro u hu hus
    apply f.conserve u hus
    intro hut
    exact ht (hut ▸ hu)
  · exact fun h => (h hs).elim

/-- Positive residual capacity, including cancellation of a reverse flow. -/
def residual (f : Flow c s t) : Digraph V where
  Adj u v := f.amount u v < (c u v : ℤ)

end Flow

/-- Ordinary directed cut capacity, counting only arcs leaving the set. -/
def cutCapacity (c : Capacity V) (X : Finset V) : ℕ :=
  ∑ u ∈ X, ∑ v ∈ Xᶜ, c u v

/-- Every feasible integral flow is bounded by every separating directed cut. -/
theorem weak_duality {c : Capacity V} {s t : V} (f : Flow c s t)
    (X : Finset V) (hs : s ∈ X) (ht : t ∉ X) : f.value ≤ (cutCapacity c X : ℤ) := by
  rw [← f.cutFlux_eq_value X hs ht]
  unfold Flow.cutFlux cutCapacity
  push_cast
  apply Finset.sum_le_sum
  intro u hu
  exact Finset.sum_le_sum fun v hv => f.upper u v

/-- A residual-closed separating cut is a genuine optimality certificate. -/
theorem value_eq_cut_of_residual_closed {c : Capacity V} {s t : V}
    (f : Flow c s t) (X : Finset V) (hs : s ∈ X) (ht : t ∉ X)
    (hclosed : ∀ u ∈ X, ∀ v, f.residual.Adj u v → v ∈ X) :
    f.value = (cutCapacity c X : ℤ) := by
  rw [← f.cutFlux_eq_value X hs ht]
  unfold Flow.cutFlux cutCapacity
  push_cast
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hn : v ∉ X := Finset.mem_compl.mp hv
  apply le_antisymm (f.upper u v)
  apply le_of_not_gt
  intro hlt
  exact hn (hclosed u hu v hlt)

/-- The certificate simultaneously proves maximum flow and minimum cut. -/
theorem optimal_of_residual_closed {c : Capacity V} {s t : V}
    (f : Flow c s t) (X : Finset V) (hs : s ∈ X) (ht : t ∉ X)
    (hclosed : ∀ u ∈ X, ∀ v, f.residual.Adj u v → v ∈ X) :
    (∀ g : Flow c s t, g.value ≤ f.value) ∧
      (∀ Y : Finset V, s ∈ Y → t ∉ Y → cutCapacity c X ≤ cutCapacity c Y) := by
  have heq := value_eq_cut_of_residual_closed f X hs ht hclosed
  constructor
  · intro g
    rw [heq]
    exact weak_duality g X hs ht
  · intro Y hsY htY
    have h := weak_duality f Y hsY htY
    rw [heq] at h
    exact_mod_cast h


/-- The actual vertices reachable by finite residual walks. The forthcoming
finite search implementation will compute this set; no search oracle is an
assumption of the certificate theorem. -/
def residualReachable {c : Capacity V} {s t : V} (f : Flow c s t) : Finset V :=
  Finset.univ.filter fun v => Nonempty (DirectedWalk f.residual s v)

omit [DecidableEq V] in
@[simp] theorem mem_residualReachable {c : Capacity V} {s t v : V}
    (f : Flow c s t) : v ∈ residualReachable f ↔
      Nonempty (DirectedWalk f.residual s v) := by
  simp [residualReachable]

omit [DecidableEq V] in
theorem source_mem_residualReachable {c : Capacity V} {s t : V}
    (f : Flow c s t) : s ∈ residualReachable f := by
  exact (mem_residualReachable f).mpr ⟨DirectedWalk.refl s⟩

omit [DecidableEq V] in
theorem residualReachable_closed {c : Capacity V} {s t : V}
    (f : Flow c s t) : ∀ u ∈ residualReachable f, ∀ v,
      f.residual.Adj u v → v ∈ residualReachable f := by
  intro u hu v huv
  obtain ⟨q⟩ := (mem_residualReachable f).mp hu
  exact (mem_residualReachable f).mpr ⟨q.append (.cons huv (.refl v))⟩

/-- Absence of an augmenting walk produces the exact cut certificate itself. -/
theorem certificate_of_no_augmenting_walk {c : Capacity V} {s t : V}
    (f : Flow c s t) (h : ¬Nonempty (DirectedWalk f.residual s t)) :
    s ∈ residualReachable f ∧ t ∉ residualReachable f ∧
      f.value = (cutCapacity c (residualReachable f) : ℤ) ∧
      (∀ g : Flow c s t, g.value ≤ f.value) ∧
      (∀ X : Finset V, s ∈ X → t ∉ X →
        cutCapacity c (residualReachable f) ≤ cutCapacity c X) := by
  have hs := source_mem_residualReachable f
  have ht : t ∉ residualReachable f := by simpa using h
  have hc := residualReachable_closed f
  exact ⟨hs, ht, value_eq_cut_of_residual_closed f _ hs ht hc,
    (optimal_of_residual_closed f _ hs ht hc).1,
    (optimal_of_residual_closed f _ hs ht hc).2⟩

end
end DirectedFlowCutGap.IntegralNetworkFlow
