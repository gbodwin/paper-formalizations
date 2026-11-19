import DirectedFlowCutGap.ResidualCutUniqueness
import DirectedFlowCutGap.FiniteGraphRelabeling

/-!
# Relabeling finite flow networks

A vertex equivalence preserves the feasible skew flows, cut capacities
and the exact sink-complement set computed by residual search.
-/

namespace DirectedFlowCutGap.IntegralFlowRelabeling

open IntegralNetworkFlow
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]

def capacity (e : A ≃ B) (c : Capacity A) : Capacity B :=
  fun u v => c (e.symm u) (e.symm v)

def flow (e : A ≃ B) {c : Capacity A} {s t : A} (f : Flow c s t) :
    Flow (capacity e c) (e s) (e t) where
  amount u v := f.amount (e.symm u) (e.symm v)
  antisymm u v := f.antisymm _ _
  upper u v := f.upper _ _
  conserve u us ut := by
    have distinct (v : A) (h : u≠e v) : e.symm u≠v := by
      intro a
      apply h
      simpa using congrArg e a
    change (∑ v : B, f.amount (e.symm u) (e.symm v))=0
    rw [e.symm.sum_comp]
    exact f.conserve _ (distinct s us) (distinct t ut)

theorem cut_capacity [DecidableEq A] [DecidableEq B] (e : A ≃ B) (c : Capacity A) (X : Finset A) :
    cutCapacity (capacity e c) (X.map e.toEmbedding)=cutCapacity c X := by
  have complement : (X.map e.toEmbedding)ᶜ=Xᶜ.map e.toEmbedding := by
    ext v
    obtain ⟨u,rfl⟩ := e.surjective v
    simp
  unfold cutCapacity
  rw [complement,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_map]
  simp [capacity]

theorem residual_adj (e : A ≃ B) {c : Capacity A} {s t : A} (f : Flow c s t) (u v : A) :
    f.residual.Adj u v ↔ (flow e f).residual.Adj (e u) (e v) := by
  simp [Flow.residual,flow,capacity]

theorem path_iff (e : A ≃ B) {c : Capacity A} {s t : A} (f : Flow c s t) (u v : A) :
    Nonempty (SimplePath f.residual u v) ↔ Nonempty (SimplePath (flow e f).residual (e u) (e v)) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨FiniteGraphRelabeling.mapPath e (residual_adj e f) p⟩
  · rintro ⟨p⟩
    have q := FiniteGraphRelabeling.mapPath e.symm (FiniteGraphRelabeling.inverse_adj e (residual_adj e f)) p
    exact ⟨by simpa only [Equiv.symm_apply_apply] using q⟩

theorem finite_cut_mem [DecidableEq A] [DecidableEq B] (e : A ≃ B) {c : Capacity A} {s t : A} (f : Flow c s t)
    (E : ResidualSearch.Enumeration A) (D : ResidualSearch.Enumeration B) (u : A) :
    e u ∈ finiteResidualCut D (flow e f) ↔ u ∈ finiteResidualCut E f := by
  rw [mem_finiteResidualCut_iff_no_walk,mem_finiteResidualCut_iff_no_walk,
    ← nonempty_simplePath_iff_directedWalk,← nonempty_simplePath_iff_directedWalk,path_iff e f u t]

end DirectedFlowCutGap.IntegralFlowRelabeling
