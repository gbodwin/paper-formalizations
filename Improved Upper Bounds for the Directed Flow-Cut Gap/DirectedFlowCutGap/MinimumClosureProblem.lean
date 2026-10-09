import DirectedFlowCutGap.Basic

/-!
# Finite signed minimum-closure instances

The input contains only finite sets and integer costs. This module defines an
actual finite combinatorial problem, not a closure optimization oracle.
-/
namespace DirectedFlowCutGap.MinimumClosureProblem

open scoped BigOperators

structure Problem (A : Type*) where
  required : Finset A
  forbidden : Finset A
  arcs : Finset (A × A)
  cost : A → ℤ

namespace Problem
variable {A : Type*} [DecidableEq A]

structure IsClosed (P : Problem A) (X : Finset A) : Prop where
  contains_required : P.required ⊆ X
  avoids_forbidden : Disjoint X P.forbidden
  follows_arcs : ∀ u v, (u, v) ∈ P.arcs → u ∈ X → v ∈ X

def objective (P : Problem A) (X : Finset A) : ℤ := ∑ v ∈ X, P.cost v

end Problem
end DirectedFlowCutGap.MinimumClosureProblem
