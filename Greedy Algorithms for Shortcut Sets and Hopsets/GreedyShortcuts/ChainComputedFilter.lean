import GreedyShortcuts.FiniteReachabilityDP
import GreedyShortcuts.ChainImportantPairs

/-! Constructive chain labels, earliest entries and the actual source filter.
Only the original Boolean adjacency and the finite chain/preprocessing data
are inputs. Reachability, labels and entry correctness are derived. -/
namespace GreedyShortcuts.ChainComputedFilter
open Finset DirectedPaths ChainFirst ChainUnion FiniteReachabilityDP
variable {n m : ℕ}

def color (T : ChainDistance.Context (Fin n) (Fin m)) (v : Fin n) : Option (Fin m) :=
  (List.finRange m).find? (fun c => decide (v∈(T.chains c).support))

theorem color_eq_label (T : ChainDistance.Context (Fin n) (Fin m)) (v : Fin n) :
    color T v=label T.chains v := by
  cases hc : color T v with
  | none =>
    have hn : ∀c,v∉(T.chains c).support := by
      simpa [color,List.find?_eq_none] using hc
    simp [label,show ¬∃c,v∈(T.chains c).support from by simpa using hn]
  | some c =>
    have hm : v∈(T.chains c).support := by
      have hp := List.find?_some hc
      simpa using hp
    exact (label_of_mem T.chains T.disjoint hm).symm

def indices (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (s : Fin n) (c : Fin m) : Finset (Fin (T.chains c).length) :=
  Finset.univ.filter (fun i => reaches edge s ((T.chains c).node i)=true)

def earliest (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (s : Fin n) (c : Fin m) : Fin n :=
  if h : (indices T edge s c).Nonempty then
    (T.chains c).node ((indices T edge s c).min' h) else s

def first (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (s v : Fin n) : Fin n :=
  match color T v with
  | none => s
  | some c => earliest T edge s c

theorem indices_eq (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (s : Fin n) (c : Fin m) : indices T edge s c=reachableIndices T.chains s c := by
  classical
  ext i
  simp [indices,reachableIndices,reaches_iff T.G T.acyclic edge he]

theorem earliest_eq (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (s : Fin n) (c : Fin m) : earliest T edge s c=entry T.chains s c := by
  classical
  unfold earliest entry
  simp only [indices_eq T edge he]

theorem first_eq (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (s v : Fin n) : first T edge s v=ChainFirst.first T.chains s v := by
  simp only [first,ChainFirst.first,color_eq_label]
  cases label T.chains v with
  | none => rfl
  | some c => exact earliest_eq T edge he s c

/-- The actual augmented fixed-source filter, constructed from original input. -/
def filtered (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (H : Finset (Fin n×Fin n))
    (s u v : Fin n) : Bool :=
  decide ((edge u v=true ∨ (u,v)∈T.base∪H) ∧
    (color T u=color T v ∨ color T v=none ∨ first T edge s v=v))

theorem filtered_iff (T : ChainDistance.Context (Fin n) (Fin m))
    (edge : Fin n → Fin n → Bool) (he : ∀u v,edge u v=true ↔ T.G u v)
    (H : Finset (Fin n×Fin n)) (s u v : Fin n) :
    filtered T edge H s u v=true ↔ T.graph H s u v := by
  simp only [filtered,decide_eq_true_eq,he,color_eq_label,first_eq T edge he]
  rfl

end GreedyShortcuts.ChainComputedFilter
