import DirectedFlowCutGap.ResidualPathSearch

/-!
# Canonical residual cuts of terminal flows

At equality in weak duality, every directed crossing arc is saturated.
Consequently every optimal separating source set is closed under the
residual arcs of every terminal flow. Source reachability gives the
least of these sets. The executable sink search gives the greatest.
Both are independent of augmenting-path choices.
-/

namespace DirectedFlowCutGap.IntegralNetworkFlow

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {c : Capacity V} {s t : V}

theorem residual_closed_of_value_eq_cut (f : Flow c s t)
    (X : Finset V) (hs : s ∈ X) (ht : t ∉ X) (he : f.value=(cutCapacity c X : ℤ)) :
    ∀ u ∈ X, ∀ v, f.residual.Adj u v → v ∈ X := by
  let slack (u v : V) : ℤ := (c u v : ℤ)-f.amount u v
  have nonneg (u v : V) : 0 ≤ slack u v := sub_nonneg.mpr (f.upper u v)
  have rows (u : V) : 0 ≤ ∑ v ∈ Xᶜ, slack u v :=
    Finset.sum_nonneg (fun v _ => nonneg u v)
  have zero : (∑ u ∈ X, ∑ v ∈ Xᶜ, slack u v)=0 := by
    simp only [slack,Finset.sum_sub_distrib]
    have cost : (∑ u ∈ X, ∑ v ∈ Xᶜ, (c u v : ℤ)) = (cutCapacity c X : ℤ) := by
      simp [cutCapacity]
    rw [cost]
    change (cutCapacity c X : ℤ)-f.cutFlux X=0
    rw [f.cutFlux_eq_value X hs ht,he,sub_self]
  have satRows := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => rows u)).mp zero
  intro u hu v edge
  by_contra hn
  have hv : v ∈ Xᶜ := Finset.mem_compl.mpr hn
  have sat := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => nonneg u v)).mp (satRows u hu) v hv
  have : 0 < slack u v := sub_pos.mpr edge
  omega

omit [DecidableEq V] in
private theorem mem_of_residual_walk (f : Flow c s t) (X : Finset V)
    (closed : ∀ u ∈ X, ∀ v, f.residual.Adj u v → v ∈ X)
    {u v : V} (p : DirectedWalk f.residual u v) : u ∈ X → v ∈ X := by
  induction p with
  | refl u => exact id
  | cons edge rest ih => exact fun hu => ih (closed _ hu _ edge)

omit [DecidableEq V] in
theorem reachable_subset_residual_closed (f : Flow c s t)
    (X : Finset V) (hs : s ∈ X)
    (closed : ∀ u ∈ X, ∀ v, f.residual.Adj u v → v ∈ X) :
    residualReachable f ⊆ X := by
  intro v hv
  obtain ⟨p⟩ := (mem_residualReachable f).mp hv
  exact mem_of_residual_walk f X closed p hs

theorem residualReachable_eq_of_terminal (f g : Flow c s t)
    (hf : ¬Nonempty (DirectedWalk f.residual s t))
    (hg : ¬Nonempty (DirectedWalk g.residual s t)) :
    residualReachable f = residualReachable g := by
  obtain ⟨fsource,fsink,fcap,fmax,_⟩ := certificate_of_no_augmenting_walk f hf
  obtain ⟨gsource,gsink,gcap,gmax,_⟩ := certificate_of_no_augmenting_walk g hg
  have equal : f.value=g.value := le_antisymm (gmax f) (fmax g)
  apply Finset.Subset.antisymm
  · refine reachable_subset_residual_closed f _ gsource ?_
    exact residual_closed_of_value_eq_cut f _ gsource gsink (equal.trans gcap)
  · refine reachable_subset_residual_closed g _ fsource ?_
    exact residual_closed_of_value_eq_cut g _ fsource fsink (equal.symm.trans fcap)

/-- The computed cut contains precisely those vertices without a walk to the sink. -/
theorem mem_finiteResidualCut_iff_no_walk (E : ResidualSearch.Enumeration V)
    (f : Flow c s t) (v : V) :
    v ∈ finiteResidualCut E f ↔ ¬Nonempty (DirectedWalk f.residual v t) := by
  let : DecidableRel f.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (f.amount u v < (c u v : ℤ)))
  change v ∈ ResidualSearch.separatingCut E f.residual t ↔ _
  rw [ResidualSearch.separatingCut, Finset.mem_compl, ResidualSearch.mem_searchTable_iff,
    nonempty_simplePath_iff_directedWalk]

theorem residual_closed_subset_finiteResidualCut (E : ResidualSearch.Enumeration V)
    (f : Flow c s t) (X : Finset V) (ht : t ∉ X)
    (closed : ∀ u ∈ X, ∀ v, f.residual.Adj u v → v ∈ X) : X ⊆ finiteResidualCut E f := by
  intro v hv
  apply (mem_finiteResidualCut_iff_no_walk E f v).mpr
  rintro ⟨p⟩
  exact ht (mem_of_residual_walk f X closed p hv)

/-- The solver's sink-complement cut agrees across terminal flows and enumerations. -/
theorem finiteResidualCut_eq_of_terminal (E D : ResidualSearch.Enumeration V)
    (f g : Flow c s t)
    (hf : ¬Nonempty (SimplePath f.residual s t))
    (hg : ¬Nonempty (SimplePath g.residual s t)) :
    finiteResidualCut E f = finiteResidualCut D g := by
  obtain ⟨fsource,fsink,fcap,fmax,_⟩ := finiteResidualCut_certificate E f hf
  obtain ⟨gsource,gsink,gcap,gmax,_⟩ := finiteResidualCut_certificate D g hg
  have equal : f.value = g.value := le_antisymm (gmax f) (fmax g)
  apply Finset.Subset.antisymm
  · exact residual_closed_subset_finiteResidualCut D g _ fsink
      (residual_closed_of_value_eq_cut g _ fsource fsink (equal.symm.trans fcap))
  · exact residual_closed_subset_finiteResidualCut E f _ gsink
      (residual_closed_of_value_eq_cut f _ gsource gsink (equal.trans gcap))

end DirectedFlowCutGap.IntegralNetworkFlow
