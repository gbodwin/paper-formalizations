import DirectedFlowCutGap.ConcurrentEdgeCover

/-! A demanded pair disconnected by removal of the free arcs certifies a
zero-cost normalized cover. The check uses the exact binary path oracle. -/
namespace DirectedFlowCutGap.ConcurrentEdgeZeroPrices

open scoped BigOperators NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph decodeCost)
open RationalEdgeThresholds (Weights weights cost)
open ConcurrentEdgeOracle (Edge)
open SparsestEdgeBridge (demandDistance)

variable {m n : ℕ}

def rawPrice (c : Weights n) (e : Edge n) : ℚ≥0 := (decodeCost (cost c) e).value

theorem rawPrice_eq (c : Weights n) (e : Edge n) : (rawPrice c e : ℝ≥0) = weights c e :=
  rfl

def positiveGraph (A : Adjacency n) (c : Weights n) : Adjacency n :=
  Vector.ofFn fun u => Vector.ofFn fun v => A[u.val][v.val] && decide (0 < rawPrice c (u,v))

theorem adj_iff (A : Adjacency n) (c : Weights n) (u v : Fin n) :
    (graph (positiveGraph A c)).Adj u v ↔ (graph A).Adj u v ∧ 0 < weights c (u,v) := by
  change (positiveGraph A c)[u.val][v.val] = true ↔ A[u.val][v.val] = true ∧ 0 < weights c (u,v)
  simp only [positiveGraph, Vector.getElem_ofFn, Bool.and_eq_true, decide_eq_true_eq]
  have equal := rawPrice_eq c (u,v)
  rw [← equal]
  constructor
  · rintro ⟨arc, h⟩
    exact ⟨arc, by exact_mod_cast h⟩
  · rintro ⟨arc, h⟩
    exact ⟨arc, by exact_mod_cast h⟩

def detect (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) : Option (Fin m) :=
  let G := positiveGraph A c
  (List.finRange m).find? fun d =>
    (RationalSparsestEdgeDistances.distance G c (P.get d)).isNone

private theorem absent_iff (A : Adjacency n) (c : Weights n) (e : Edge n) :
    (RationalSparsestEdgeDistances.distance (positiveGraph A c) c e).isNone = true ↔
      ¬Nonempty (SimplePath (graph (positiveGraph A c)) e.1 e.2) := by
  rw [← edgeDistance_eq_top_iff _ (weights c), ← RationalSparsestEdgeDistances.none_iff]
  cases RationalSparsestEdgeDistances.distance (positiveGraph A c) c e <;> simp

theorem detected {A : Adjacency n} {c : Weights n} {P : Vector (Edge n) m} {d : Fin m}
    (found : detect A c P = some d) :
    ¬Nonempty (SimplePath (graph (positiveGraph A c)) (P.get d).1 (P.get d).2) := by
  apply (absent_iff A c (P.get d)).mp
  exact List.find?_some (p := fun i : Fin m =>
    (RationalSparsestEdgeDistances.distance (positiveGraph A c) c (P.get i)).isNone) found

theorem all_reachable {A : Adjacency n} {c : Weights n} {P : Vector (Edge n) m}
    (none : detect A c P = none) :
    ∀ d : Fin m, Nonempty (SimplePath (graph (positiveGraph A c)) (P.get d).1 (P.get d).2) := by
  classical
  intro d
  by_contra unreachable
  have present := (absent_iff A c (P.get d)).mpr unreachable
  have missing := (List.find?_eq_none.mp none) d (List.mem_finRange d)
  simp [present] at missing

def freeLength (c : Weights n) (m : ℕ) : Weights n :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    let w : ℚ≥0 := if 0 < rawPrice c (u,v) then 0 else m
    (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat w)).1

theorem freeLength_eq (c : Weights n) (m : ℕ) (e : Edge n) :
    weights (freeLength c m) e = if 0 < weights c e then 0 else (m : ℝ≥0) := by
  rcases e with ⟨u,v⟩
  have observed : (decodeCost (cost (freeLength c m)) (u,v)).value =
      if 0 < rawPrice c (u,v) then 0 else (m : ℚ≥0) := by
    simp only [cost, decodeCost, freeLength, Vector.getElem_ofFn, BinaryRawRational.encode_value,
      RawNonnegativeRational.Code.value_ofNNRat]
  change (((decodeCost (cost (freeLength c m)) (u,v)).value : ℚ≥0) : ℝ≥0) = _
  rw [observed]
  by_cases price : 0 < rawPrice c (u,v)
  · have real : 0 < weights c (u,v) := by
      rw [← rawPrice_eq]
      exact_mod_cast price
    rw [ite_eq_left price, ite_eq_left real, NNRat.cast_zero]
  · have real : ¬0 < weights c (u,v) := by
      rw [← rawPrice_eq]
      exact_mod_cast price
    rw [ite_eq_right price, ite_eq_right real, NNRat.cast_natCast]

theorem free_objective (A : Adjacency n) (c : Weights n) (m : ℕ) :
    weightedEdgeCost (graph A) (weights c) (weights (freeLength c m)) = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  rw [freeLength_eq]
  by_cases h : 0 < weights c e
  · rw [ite_eq_left h, mul_zero]
  · have z : weights c e = 0 := le_antisymm (le_of_not_gt h) zero_le
    rw [z, zero_mul]

theorem free_normalized (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (d : Fin m)
    (reachable : Nonempty (SimplePath (graph A) (P.get d).1 (P.get d).2))
    (freeRequired : ¬Nonempty (SimplePath (graph (positiveGraph A c)) (P.get d).1 (P.get d).2)) :
    (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights (freeLength c m)) (P.get j) := by
  let w := weights (freeLength c m)
  let e := P.get d
  have pathBound : ((m : ℝ≥0) : ℝ≥0∞) ≤ edgeDistance (graph A) w e.1 e.2 := by
    apply (coe_le_edgeDistance_iff (graph A) w e.1 e.2 _).mpr
    intro p
    have existsFree : ∃ a ∈ p.edges, ¬0 < weights c a := by
      by_contra! all
      apply freeRequired
      refine ⟨{ p with adjacent := fun i => ?_ }⟩
      exact (adj_iff A c _ _).mpr ⟨p.adjacent i, all _ (p.edgeAt_mem_edges i)⟩
    obtain ⟨a,inside,zero⟩ := existsFree
    have h : w a = m := by
      change weights (freeLength c m) a = _
      rw [freeLength_eq, ite_eq_right zero]
    exact h.ge.trans (Finset.single_le_sum (f := w) (fun _ _ => zero_le) inside)
  have finite : edgeDistance (graph A) w e.1 e.2 ≠ ⊤ :=
    fun top => ((edgeDistance_eq_top_iff (graph A) w e.1 e.2).mp top) reachable
  rw [← ENNReal.coe_toNNReal finite] at pathBound
  exact (ENNReal.coe_le_coe.mp pathBound).trans (Finset.single_le_sum
    (f := fun j : Fin m => demandDistance (graph A) w (P.get j)) (fun _ _ => zero_le) (Finset.mem_univ d))

end DirectedFlowCutGap.ConcurrentEdgeZeroPrices
