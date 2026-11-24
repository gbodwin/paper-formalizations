import DirectedFlowCutGap.SparsestNormalizedPotentials
import DirectedFlowCutGap.RationalSparsestVertexDistances

/-! Normalize endpoint-excluding vertex distances with a separate potential
for each demand. The arc leaving that demand's source has zero length. -/
namespace DirectedFlowCutGap.VertexNormalizedPotentials

open scoped BigOperators NNReal ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open SparsestVertexBridge (demandDistance)

variable {m n : ℕ}

def departure (w : Fin n → ℝ≥0) (s : Fin n) (e : Fin n × Fin n) : ℝ≥0 :=
  if e.1 = s then 0 else w e.1

theorem path_weight {G : Digraph (Fin n)} {s t : Fin n} (p : SimplePath G s t)
    (w : Fin n → ℝ≥0) : p.edgeWeight (departure w s) = p.weight w := by
  have tail_set :
      ((p.edges.filter fun e => e.1 ≠ s).image Prod.fst) = p.internalVertices := by
    rw [← FractionalCoverGraphOracle.internalColumn_eq p]
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, FractionalCoverGraphOracle.internalColumn,
      Finset.mem_erase, List.mem_toFinset, List.mem_map, IntegralNetworkFlow.Tabulated.FlowTable.mem_edgeList]
    constructor
    · rintro ⟨e,⟨present,nonSource⟩,rfl⟩
      have nonTarget : e.1 ≠ t := by
        obtain ⟨i,rfl⟩ := (p.mem_edges e).mp present
        intro equal
        have same := congrArg Fin.val (p.injective (equal.trans p.target_eq.symm))
        change i.val = p.edgeLength at same
        exact (Nat.ne_of_lt i.isLt) same
      exact ⟨nonTarget,nonSource,e,present,rfl⟩
    · rintro ⟨_,nonSource,e,present,rfl⟩
      exact ⟨e,⟨present,nonSource⟩,rfl⟩
  have injective : Set.InjOn Prod.fst (↑(p.edges.filter fun e => e.1 ≠ s) : Set (Fin n × Fin n)) := by
    intro e present f follows equal
    obtain ⟨i,rfl⟩ := (p.mem_edges e).mp (Finset.mem_filter.mp present).1
    obtain ⟨j,rfl⟩ := (p.mem_edges f).mp (Finset.mem_filter.mp follows).1
    have same : i = j := Fin.ext (congrArg (fun k : Fin (p.edgeLength+1) => k.val) (p.injective equal))
    exact congrArg p.edgeAt same
  unfold SimplePath.edgeWeight SimplePath.weight
  rw [← tail_set, Finset.sum_image injective, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases source : e.1 = s <;> simp [departure,source]

theorem distance_eq (G : Digraph (Fin n)) (w : Fin n → ℝ≥0) (s t : Fin n) :
    edgeDistance G (departure w s) s t = vertexDistance G w s t := by
  unfold edgeDistance vertexDistance
  exact iInf_congr fun p => congrArg (fun q : ℝ≥0 => (q : ℝ≥0∞)) (path_weight p w)

structure Feasible (G : Digraph (Fin n)) (w : Fin n → ℝ≥0) (P : Fin m → Fin n × Fin n)
    (target : ℝ≥0) (p : Fin m → Fin n → ℝ≥0) : Prop where
  origin : ∀ i, p i (P i).1 = 0
  step : ∀ i u v, G.Adj u v → p i v ≤ p i u + departure w (P i).1 (u,v)
  normalize : target ≤ ∑ i, p i (P i).2

noncomputable section

theorem normalization_iff (G : Digraph (Fin n)) (w : Fin n → ℝ≥0) (P : Fin m → Fin n × Fin n)
    (target : ℝ≥0) (reach : ∀ i, Nonempty (SimplePath G (P i).1 (P i).2)) :
    (∃ p, Feasible G w P target p) ↔ target ≤ ∑ i, demandDistance G w (P i) := by
  have finite (i : Fin m) : vertexDistance G w (P i).1 (P i).2 ≠ ⊤ :=
    fun h => ((vertexDistance_eq_top_iff G w _ _).mp h) (reach i)
  constructor
  · rintro ⟨p,fit⟩
    apply fit.normalize.trans
    apply Finset.sum_le_sum
    intro i _
    have bound := SparsestNormalizedPotentials.potential_le_distance G (departure w (P i).1)
      (p i) (P i).1 (P i).2 (fit.origin i) (fit.step i)
    rw [distance_eq, ← ENNReal.coe_toNNReal (finite i)] at bound
    exact ENNReal.coe_le_coe.mp bound
  · intro enough
    let p (i : Fin m) (v : Fin n) :=
      SparsestNormalizedPotentials.capped G (departure w (P i).1) target (P i).1 v
    refine ⟨p,⟨?_,?_,?_⟩⟩
    · intro i
      simp [p,SparsestNormalizedPotentials.capped]
    · intro i u v arc
      exact SparsestNormalizedPotentials.capped_arc G (departure w (P i).1) target (P i).1 u v arc
    · have atSink (i : Fin m) : p i (P i).2 = min (demandDistance G w (P i)) target := by
        apply ENNReal.coe_injective
        change (SparsestNormalizedPotentials.capped G (departure w (P i).1) target (P i).1 (P i).2 : ℝ≥0∞) = _
        rw [SparsestNormalizedPotentials.capped_value,distance_eq,ENNReal.coe_min,demandDistance,
          ENNReal.coe_toNNReal (finite i)]
      simp only [atSink]
      classical
      by_cases all : ∀ i, demandDistance G w (P i) ≤ target
      · simpa only [fun i => min_eq_left (all i)] using enough
      · obtain ⟨i,large⟩ := not_forall.mp all
        have one := Finset.single_le_sum (f := fun i => min (demandDistance G w (P i)) target)
          (fun _ _ => zero_le) (Finset.mem_univ i)
        rwa [min_eq_right (le_of_not_ge large)] at one

theorem normalized_of_nonadjacent (G : Digraph (Fin n)) (P : Fin m → Fin n × Fin n)
    (target : ℝ≥0) (i : Fin m) (reach : Nonempty (SimplePath G (P i).1 (P i).2))
    (different : (P i).1 ≠ (P i).2) (noArc : ¬G.Adj (P i).1 (P i).2) :
    target ≤ ∑ j, demandDistance G (fun _ => target) (P j) := by
  let w : Fin n → ℝ≥0 := fun _ => target
  have finite : vertexDistance G w (P i).1 (P i).2 ≠ ⊤ :=
    fun h => ((vertexDistance_eq_top_iff G w _ _).mp h) reach
  have far : (target : ℝ≥0∞) ≤ vertexDistance G w (P i).1 (P i).2 := by
    apply (coe_le_vertexDistance_iff G w _ _ _).mpr
    intro path
    obtain ⟨v,present⟩ := FractionalCoverGraphOracle.internal_nonempty_of_nonadjacent path different noArc
    exact Finset.single_le_sum (f := w) (fun _ _ => zero_le) present
  rw [← ENNReal.coe_toNNReal finite] at far
  exact (ENNReal.coe_le_coe.mp far).trans
    (Finset.single_le_sum (f := fun j => demandDistance G w (P j)) (fun _ _ => zero_le) (Finset.mem_univ i))

end
end DirectedFlowCutGap.VertexNormalizedPotentials
