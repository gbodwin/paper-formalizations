import DirectedFlowCutGap.IntegralNetworkFlow

/-!
# Unit augmentation along genuine residual paths

The update sends one unit along each actual path edge and cancels the reverse
flow. Integer residual capacity ensures feasibility, and path telescoping
preserves every internal conservation law. No augmenting-path oracle is assumed
in these algebraic lemmas; a search implementation is a separate component.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The directed unit signal of the actual edge set of a simple path. -/
def pathSignal {G : Digraph V} {s t : V} (p : SimplePath G s t) (u v : V) : ℤ :=
  if (u,v) ∈ p.edges then 1 else 0

omit [Fintype V] in
theorem pathSignal_eq_sum {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (u v : V) :
    pathSignal p u v = ∑ i : Fin p.edgeLength,
      if p.edgeAt i = (u,v) then (1 : ℤ) else 0 := by
  calc
    _ = ∑ e ∈ p.edges, if e = (u,v) then (1 : ℤ) else 0 := by simp [pathSignal]
    _ = _ := Finset.sum_image (fun i _ j _ hij => p.edgeAt_injective hij)

theorem pathSignal_out {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (v : V) :
    (∑ u, pathSignal p v u) = ∑ i : Fin p.edgeLength,
      if p.vertex i.castSucc = v then (1 : ℤ) else 0 := by
  simp_rw [pathSignal_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : p.vertex i.castSucc = v <;> simp [SimplePath.edgeAt, Prod.mk.injEq, h]

theorem pathSignal_in {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (v : V) :
    (∑ u, pathSignal p u v) = ∑ i : Fin p.edgeLength,
      if p.vertex i.succ = v then (1 : ℤ) else 0 := by
  simp_rw [pathSignal_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : p.vertex i.succ = v <;> simp [SimplePath.edgeAt, Prod.mk.injEq, h]

/-- All internal path contributions telescope, with exact source/sink signs. -/
theorem pathSignal_divergence {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (v : V) :
    (∑ u, pathSignal p v u) - (∑ u, pathSignal p u v) =
      (if s = v then (1 : ℤ) else 0) - (if t = v then 1 else 0) := by
  rw [pathSignal_out, pathSignal_in]
  have h₁ := Fin.sum_univ_castSucc (fun j : Fin (p.edgeLength + 1) =>
    if p.vertex j = v then (1 : ℤ) else 0)
  have h₂ := Fin.sum_univ_succ (fun j : Fin (p.edgeLength + 1) =>
    if p.vertex j = v then (1 : ℤ) else 0)
  simp only [p.source_eq, p.target_eq] at h₁ h₂
  omega

/-- A genuine feasible flow after one unit is sent along a residual path. -/
def Flow.augment {c : Capacity V} {s t : V} (f : Flow c s t)
    (p : SimplePath f.residual s t) : Flow c s t where
  amount := fun u v => f.amount u v + pathSignal p u v - pathSignal p v u
  antisymm := by
    intro u v
    rw [f.antisymm u v]
    ring
  upper := by
    intro u v
    by_cases hp : (u,v) ∈ p.edges
    · have hres : f.amount u v < (c u v : ℤ) := p.edge_adj hp
      by_cases hr : (v,u) ∈ p.edges <;> simp only [pathSignal, hp, hr, ite_true, ite_false] <;> omega
    · have hc := f.upper u v
      by_cases hr : (v,u) ∈ p.edges <;> simp only [pathSignal, hp, hr, ite_true, ite_false] <;> omega
  conserve := by
    intro v hvs hvt
    have hf := f.conserve v hvs hvt
    have hp := pathSignal_divergence p v
    have hsn : s ≠ v := Ne.symm hvs
    have htn : t ≠ v := Ne.symm hvt
    simp only [hsn, htn, ite_false, sub_self] at hp
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    omega

/-- Source value increases by exactly one; the distinct-endpoint hypothesis
is explicit and no positive self augmentation is counted. -/
theorem Flow.augment_value {c : Capacity V} {s t : V} (f : Flow c s t)
    (p : SimplePath f.residual s t) (hst : s ≠ t) :
    (f.augment p).value = f.value + 1 := by
  have hp := pathSignal_divergence p s
  have hts : t ≠ s := Ne.symm hst
  simp only [hts, ite_true, ite_false, sub_zero] at hp
  simp only [Flow.value, Flow.divergence, Flow.augment,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  omega

/-- Once a feasible flow reaches a separating cut's capacity, no residual
source-to-sink path can exist. -/
theorem no_path_of_value_eq_cut {c : Capacity V} {s t : V} (f : Flow c s t)
    (X : Finset V) (hs : s ∈ X) (ht : t ∉ X)
    (hvalue : f.value = (cutCapacity c X : ℤ)) :
    ¬Nonempty (SimplePath f.residual s t) := by
  rintro ⟨p⟩
  have hst : s ≠ t := by intro h; exact ht (h ▸ hs)
  have hb := weak_duality (f.augment p) X hs ht
  rw [f.augment_value p hst, hvalue] at hb
  omega

end
end DirectedFlowCutGap.IntegralNetworkFlow
