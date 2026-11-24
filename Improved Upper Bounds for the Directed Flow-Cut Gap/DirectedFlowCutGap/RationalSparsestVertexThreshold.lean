import DirectedFlowCutGap.RationalSparsestVertexDistances
import DirectedFlowCutGap.RationalSparsestEdgeThreshold

/-! The same harmonic selector on exact endpoint-safe vertex distances. -/
namespace DirectedFlowCutGap.RationalSparsestVertexThreshold

open scoped BigOperators NNReal NNRat ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RationalSparsestVertexDistances (weights distance)
open RationalSparsestEdgeThreshold (Selection select table_spec)
open FiniteHarmonicThreshold (above harmonicWeight)

variable {m n : ℕ}

def table (A : Adjacency n) (w : Row n) (P : Vector (Fin n × Fin n) m) :
    Vector (Option ℚ≥0) m := P.map (distance A w)

def choose (A : Adjacency n) (w : Row n) (P : Vector (Fin n × Fin n) m) : Selection m :=
  select (table A w P)

noncomputable def actualDistance (A : Adjacency n) (w : Row n)
    (P : Vector (Fin n × Fin n) m) (i : Fin m) : ℝ≥0 :=
  SparsestVertexBridge.demandDistance (graph A) (weights w) P[i.val]

theorem choose_spec (A : Adjacency n) (w : Row n) (P : Vector (Fin n × Fin n) m) :
    let D := actualDistance A w P
    match choose A w P with
    | .unreachable i => vertexDistance (graph A) (weights w) P[i.val].1 P[i.val].2 = ⊤
    | .zero => ∀ i : Fin m, vertexDistance (graph A) (weights w) P[i.val].1 P[i.val].2 = 0
    | .threshold i τ =>
      (∀ j : Fin m, vertexDistance (graph A) (weights w) P[j.val].1 P[j.val].2 ≠ ⊤) ∧
      D i = (τ : ℝ≥0) ∧ 0 < τ ∧ 0 < (above D (τ : ℝ≥0)).card ∧
        (∑ j, D j) ≤ harmonicWeight m * ((τ : ℝ≥0)*((above D (τ : ℝ≥0)).card : ℝ≥0)) := by
  let entries := table A w P
  let real := actualDistance A w P
  let raw (j : Fin m) := entries[j.val].getD 0
  have cell (j : Fin m) : entries[j.val] = distance A w P[j.val] := by
    simp only [entries, table, Vector.getElem_map]
  have info := table_spec entries
  unfold choose
  dsimp only
  cases picked : select entries with
  | unreachable i =>
    rw [picked] at info
    have none : entries[i.val] = none := info
    rw [cell] at none
    exact (RationalSparsestVertexDistances.none_iff A w _).mp none
  | zero =>
    rw [picked] at info
    intro i
    have empty : entries[i.val] = some 0 := info i
    rw [cell] at empty
    rw [← RationalSparsestVertexDistances.distance_exact A w P[i.val], empty]
    simp [RationalSparsestEdgeDistances.observe]
  | threshold i τ =>
    rw [picked] at info
    obtain ⟨present, atIndex, positive, nonempty, score⟩ := info
    have exact (j : Fin m) : (raw j : ℝ≥0) = real j :=
      RationalSparsestVertexDistances.finite_value A w P[j.val] ((cell j).symm.trans (present j))
    have attained : (τ : ℝ≥0) = real i :=
      RationalSparsestVertexDistances.finite_value A w P[i.val] ((cell i).symm.trans atIndex)
    have counts : RationalHarmonicThreshold.count raw τ = (above real (τ : ℝ≥0)).card := by
      rw [RationalHarmonicThreshold.count_cast, funext exact]
    change 0 < RationalHarmonicThreshold.count raw τ at nonempty
    change (∑ j, (raw j : ℝ≥0)) ≤ harmonicWeight m *
      ((τ : ℝ≥0) * (RationalHarmonicThreshold.count raw τ : ℝ≥0)) at score
    refine ⟨?_, attained.symm, positive, counts ▸ nonempty, ?_⟩
    · intro j top
      have none := (RationalSparsestVertexDistances.none_iff A w _).mpr top
      rw [← cell j, present j] at none
      cases none
    · rw [counts] at score
      simpa only [exact] using score

end DirectedFlowCutGap.RationalSparsestVertexThreshold
