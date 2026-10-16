import LightEFTSpanners.NativeForestCardinality
import Mathlib.Data.Setoid.Basic

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph
variable {V E : Type*}

/-- Keep exactly the graph edges whose endpoints lie in the same supplied
partition class. Reachability in this graph is genuine within-block reachability. -/
def blockGraph (H : SimpleGraph V) (R : Setoid V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ R.r u v
  symm.symm _ _ h := ⟨h.1.symm,R.symm h.2⟩
  loopless.irrefl _ h := h.1.ne rfl

theorem blockGraph_le (H : SimpleGraph V) (R : Setoid V) : blockGraph H R≤H :=
  fun _ _ h => h.1

theorem blockGraph_reachable_rel (H : SimpleGraph V) (R : Setoid V)
    {u v : V} (h : (blockGraph H R).Reachable u v) : R.r u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact R.refl _
  | cons h p ih => exact R.trans h.2 ih

/-- Refining by the actual connected components inside every partition block. -/
def componentRefinement (H : SimpleGraph V) (R : Setoid V) : Setoid V :=
  (blockGraph H R).reachableSetoid

theorem componentRefinement_le (H : SimpleGraph V) (R : Setoid V) :
    componentRefinement H R≤R := fun _ _ h => blockGraph_reachable_rel H R h

theorem componentRefinement_eq_iff (H : SimpleGraph V) (R : Setoid V) :
    componentRefinement H R=R ↔
      ∀ u v,R.r u v → (blockGraph H R).Reachable u v := by
  constructor
  · intro h u v huv
    exact (congrArg (fun T : Setoid V => T.r u v) h).mpr huv
  · intro h
    exact le_antisymm (componentRefinement_le H R) h

theorem componentRefinement_mono (H : SimpleGraph V) {R S : Setoid V} (hRS : R≤S) :
    componentRefinement H R≤componentRefinement H S := by
  intro u v h
  exact h.mono (show blockGraph H R≤blockGraph H S from
    fun _ _ hadj => ⟨hadj.1,hRS hadj.2⟩)

/-- After refining once by a color, each new block is genuinely connected in
that color; applying the same component refinement again has no effect. -/
theorem componentRefinement_idempotent (H : SimpleGraph V) (R : Setoid V) :
    componentRefinement H (componentRefinement H R)=componentRefinement H R := by
  have heq : blockGraph H (componentRefinement H R)=blockGraph H R := by
    ext u v
    constructor
    · intro h
      exact ⟨h.1,componentRefinement_le H R h.2⟩
    · intro h
      exact ⟨h.1,(show (blockGraph H R).Adj u v from h).reachable⟩
  exact congrArg SimpleGraph.reachableSetoid heq

/-- A disconnected supplied block forces a strict partition refinement. -/
theorem componentRefinement_lt (H : SimpleGraph V) (R : Setoid V)
    {u v : V} (hR : R.r u v) (hnot : ¬(blockGraph H R).Reachable u v) :
    componentRefinement H R<R := by
  refine lt_of_le_of_ne (componentRefinement_le H R) ?_
  intro heq
  exact hnot ((componentRefinement_eq_iff H R).mp heq u v hR)

/-- Native color refinement uses actual native vertices and the surviving
original-edge subgraph; parallel identities affect color membership before
ordinary within-block reachability is formed. -/
def nativeColorRefinement (G : Graph V E) (F : Set E) (R : Setoid G.vertexSet) :
    Setoid G.vertexSet := componentRefinement (G.restrict F).toSimpleGraph R
end LightEFTSpanners.MultigraphCuts
