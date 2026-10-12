import GreedyShortcuts.ChainComputedFilter

/-! Executable original important demands, raw objective and stopping test.
The finite original adjacency, chain nodes and preprocessing edges are given;
there is no supplied minimum-distance, reachability, label or entry oracle.
This correctness result does not assert a physical runtime bound. -/
namespace GreedyShortcuts.ChainExecutableObjective
open Finset DirectedPaths ChainFirst ChainComputedFilter
variable {n m : ℕ}

def demands (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) : Finset (Fin n×Fin n) :=
  (Finset.univ.filter (fun sc : Fin n×Fin m =>
    (indices T edge sc.1 sc.2).Nonempty)).image
    (fun sc => (sc.1,earliest T edge sc.1 sc.2))

def distance (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (H : Finset (Fin n×Fin n)) (s t : Fin n) : ℕ :=
  ChainDistanceDP.evaluate (filtered T edge H s) (color T) s t

def potential (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (H : Finset (Fin n×Fin n)) : ℕ :=
  ∑ st∈demands T edge,distance T edge H st.1 st.2

def stopped (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (D : ℕ) (H : Finset (Fin n×Fin n)) : Bool :=
  decide (∀st∈demands T edge,distance T edge H st.1 st.2≤D)

theorem demands_eq (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v) :
    demands T edge=T.important := by
  classical
  simp only [demands,ChainDistance.Context.important,ChainDistance.Context.active,
    indices_eq T edge he,earliest_eq T edge he]

theorem distance_eq (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (H : Finset (Fin n×Fin n)) (hH : H⊆candidates T.G) (s t : Fin n) :
    distance T edge H s t=T.distance H s t :=
  ChainDistanceDP.evaluate_eq_distance T H hH _ _ s t
    (filtered_iff T edge he H s) (funext (color_eq_label T))

theorem potential_eq (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (H : Finset (Fin n×Fin n)) (hH : H⊆candidates T.G) :
    potential T edge H=T.potential H := by
  simp only [potential,ChainDistance.Context.potential,demands_eq T edge he,
    distance_eq T edge he H hH]

theorem stopped_iff (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (D : ℕ) (H : Finset (Fin n×Fin n)) (hH : H⊆candidates T.G) :
    stopped T edge D H=true ↔ T.stopped D H := by
  simp only [stopped,decide_eq_true_eq,ChainDistance.Context.stopped,
    demands_eq T edge he,distance_eq T edge he H hH]

end GreedyShortcuts.ChainExecutableObjective
