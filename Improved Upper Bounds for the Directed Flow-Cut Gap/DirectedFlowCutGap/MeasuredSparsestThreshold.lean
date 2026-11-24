import DirectedFlowCutGap.MeasuredSparsestDistances
import DirectedFlowCutGap.MeasuredHarmonicChoice
import DirectedFlowCutGap.MeasuredFirstResult
import DirectedFlowCutGap.RationalSparsestVertexThreshold

/-! The actual binary distance table, missing-demand search and harmonic
score choose the same threshold and witness index as the rational entry. -/
namespace DirectedFlowCutGap.MeasuredSparsestThreshold

open scoped NNRat
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)
open MeasuredBudgetPrices (tabulate tabulate_value tabulate_charge)
open MeasuredSparsestDistances (OptionFits distanceWidth)
open MeasuredFirstResult (find find_value find_charge)

variable {n m : ℕ}

inductive Selection (m : ℕ) where
  | unreachable (index : Fin m)
  | zero
  | threshold (index : Fin m) (value : Code)

def Selection.observe : Selection m → RationalSparsestEdgeThreshold.Selection m
  | .unreachable i => .unreachable i
  | .zero => .zero
  | .threshold i q => .threshold i q.value

private def finite (table : Vector (Option Code) m) (j : Fin m) : Code :=
  (table.get j).getD Code.zero

private def absent (table : Vector (Option Code) m) : Option (Fin m) × ℕ :=
  find (fun j => ((table.get j).isNone,1)) (List.finRange m)

def select (table : Vector (Option Code) m) : Selection m × ℕ :=
  let missing := absent table
  match missing.1 with
  | some i => (.unreachable i,missing.2+1)
  | none =>
    let chosen := MeasuredHarmonicChoice.choose (finite table)
    match chosen.1 with
    | none => (.zero,missing.2+chosen.2+1)
    | some i =>
      let threshold := finite table i
      let test := BinaryRawRational.le threshold Code.zero
      (if test.1 then .zero else .threshold i threshold,missing.2+chosen.2+test.2+1)

def decodeTable (table : Vector (Option Code) m) : Vector (Option ℚ≥0) m :=
  table.map (Option.map Code.value)

private theorem absent_value (table : Vector (Option Code) m) :
    (absent table).1 = (List.finRange m).find? (fun j => (decodeTable table)[j.val].isNone) := by
  simp only [absent,find_value,decodeTable,Vector.getElem_map]
  congr 1
  funext j
  change (table.get j).isNone = ((table.get j).map Code.value).isNone
  cases table.get j <;> rfl

private theorem finite_value (table : Vector (Option Code) m) (j : Fin m) :
    (finite table j).value = ((decodeTable table)[j.val]).getD 0 := by
  simp only [finite,decodeTable,Vector.getElem_map]
  change ((table.get j).getD Code.zero).value = ((table.get j).map Code.value).getD 0
  cases table.get j <;> simp

theorem select_value (table : Vector (Option Code) m) :
    (select table).1.observe = RationalSparsestEdgeThreshold.select (decodeTable table) := by
  let d := fun j : Fin m => ((decodeTable table)[j.val]).getD 0
  change (select table).1.observe =
    match (List.finRange m).find? (fun j => (decodeTable table)[j.val].isNone) with
    | some i => .unreachable i
    | none => match RationalHarmonicThreshold.choose d with
      | none => .zero
      | some i => if 0 < d i then .threshold i (d i) else .zero
  rw [← absent_value]
  cases missing : (absent table).1 with
  | some i => simp only [select,missing,Selection.observe]
  | none =>
    have picked : (MeasuredHarmonicChoice.choose (finite table)).1 = RationalHarmonicThreshold.choose d := by
      rw [MeasuredHarmonicChoice.choose_value]
      exact congrArg RationalHarmonicThreshold.choose (funext (finite_value table))
    rw [← picked]
    cases chosen : (MeasuredHarmonicChoice.choose (finite table)).1 with
    | none => simp only [select,missing,chosen,Selection.observe]
    | some i =>
      change (select table).1.observe = if 0 < d i then .threshold i (d i) else .zero
      simp only [select,missing,chosen,BinaryRawRational.le_value,Code.le_eq_true,Code.value_zero]
      obtain limit := finite_value table i
      change (finite table i).value = d i at limit
      by_cases pos : 0 < d i
      · rw [ite_eq_right (not_le_of_gt (limit.symm ▸ pos)),ite_eq_left pos,Selection.observe,limit]
      · rw [ite_eq_left (le_of_not_gt (show ¬0 < (finite table i).value from limit.symm ▸ pos)),
          ite_eq_right pos,Selection.observe]

def selectionWork (m B : ℕ) : ℕ :=
  (m*5+1)+MeasuredHarmonicChoice.chooseWork m B+BinaryRawRational.budget B+1

private theorem finite_fits (table : Vector (Option Code) m) {B : ℕ}
    (fits : ∀ j, OptionFits (table.get j) B) (j : Fin m) : (finite table j).Bounded B := by
  cases h : table.get j with
  | none =>
    simpa only [finite,h,Option.getD_none] using Code.bounded_mono Code.bounded_zero (Nat.zero_le B)
  | some q => simpa only [finite,h,Option.getD_some] using fits j q h

theorem select_threshold_fits (table : Vector (Option Code) m) {B : ℕ}
    (fits : ∀ j, OptionFits (table.get j) B) {i : Fin m} {q : Code}
    (found : (select table).1 = .threshold i q) : q.Bounded B := by
  unfold select at found
  dsimp only at found
  split at found
  · cases found
  · split at found
    · cases found
    · dsimp only at found
      split at found
      · cases found
      · cases found
        exact finite_fits table fits _

theorem select_charge (table : Vector (Option Code) m) {B : ℕ}
    (fits : ∀ j, OptionFits (table.get j) B) :
    (select table).2 ≤ selectionWork m B := by
  have findWork := find_charge (fun j => ((table.get j).isNone,1)) (List.finRange m)
    (fun _ _ => (Nat.le_refl 1))
  rw [List.length_finRange] at findWork
  change (absent table).2 ≤ m*5+1 at findWork
  have finiteFits := finite_fits table fits
  have ranked := MeasuredHarmonicChoice.choose_charge (finite table) finiteFits
  unfold select selectionWork
  dsimp only
  split
  · omega
  · split
    · omega
    · rename_i i _
      have check := BinaryRawRational.le_paid (finiteFits i)
        (Code.bounded_mono Code.bounded_zero (Nat.zero_le B))
      omega

def edge (A : Adjacency n) (w : Weights n) (P : Vector (Edge n) m) : Selection m × ℕ :=
  let table := tabulate fun j => MeasuredSparsestDistances.edge A w (P.get j)
  let selected := select table.1
  (selected.1,table.2+selected.2)

theorem edge_value (A : Adjacency n) (w : Weights n) (P : Vector (Edge n) m) :
    (edge A w P).1.observe = RationalSparsestEdgeThreshold.choose A w P := by
  unfold edge RationalSparsestEdgeThreshold.choose
  dsimp only
  rw [select_value]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [decodeTable,tabulate_value,Vector.getElem_map,
    RationalSparsestEdgeThreshold.table,MeasuredSparsestDistances.edge_value]
  rfl

def edgeWork (n m B : ℕ) : ℕ :=
  m*MeasuredSparsestDistances.edgeWork n B+selectionWork m (distanceWidth n B)

theorem edge_charge (A : Adjacency n) (w : Weights n) (P : Vector (Edge n) m) {B : ℕ}
    (fits : MatrixFits w B) : (edge A w P).2 ≤ edgeWork n m B := by
  let cells := fun j : Fin m => MeasuredSparsestDistances.edge A w (P.get j)
  have paid := tabulate_charge cells (fun j => (MeasuredSparsestDistances.edge_bounds A w (P.get j) fits).2)
  have shaped (j : Fin m) : OptionFits (tabulate cells).1[j.val] (distanceWidth n B) := by
    rw [tabulate_value]
    exact (MeasuredSparsestDistances.edge_bounds A w (P.get j) fits).1
  have chosen := select_charge (tabulate cells).1 shaped
  exact Nat.add_le_add paid chosen

theorem edge_threshold_fits (A : Adjacency n) (w : Weights n) (P : Vector (Edge n) m) {B : ℕ}
    (fits : MatrixFits w B) {i : Fin m} {q : Code}
    (found : (edge A w P).1 = .threshold i q) : q.Bounded (distanceWidth n B) := by
  let cells := fun j : Fin m => MeasuredSparsestDistances.edge A w (P.get j)
  have shaped (j : Fin m) : OptionFits (tabulate cells).1[j.val] (distanceWidth n B) := by
    rw [tabulate_value]
    exact (MeasuredSparsestDistances.edge_bounds A w (P.get j) fits).1
  exact select_threshold_fits (tabulate cells).1 shaped found

def vertex (A : Adjacency n) (w : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) : Selection m × ℕ :=
  let table := tabulate fun j => MeasuredSparsestDistances.vertex A w (P.get j)
  let selected := select table.1
  (selected.1,table.2+selected.2)

theorem vertex_value (A : Adjacency n) (w : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    (vertex A w P).1.observe = RationalSparsestVertexThreshold.choose A w P := by
  unfold vertex RationalSparsestVertexThreshold.choose
  dsimp only
  rw [select_value]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [decodeTable,tabulate_value,Vector.getElem_map,
    RationalSparsestVertexThreshold.table,MeasuredSparsestDistances.vertex_value]
  rfl

def vertexWork (n m B : ℕ) : ℕ :=
  m*MeasuredSparsestDistances.vertexWork n B+selectionWork m (distanceWidth n (max 1 B))

theorem vertex_charge (A : Adjacency n) (w : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    {B : ℕ} (fits : ∀ j, StoredBounded (w.get j) B) : (vertex A w P).2 ≤ vertexWork n m B := by
  let cells := fun j : Fin m => MeasuredSparsestDistances.vertex A w (P.get j)
  have paid := tabulate_charge cells (fun j => (MeasuredSparsestDistances.vertex_bounds A w (P.get j) fits).2)
  have shaped (j : Fin m) : OptionFits (tabulate cells).1[j.val] (distanceWidth n (max 1 B)) := by
    rw [tabulate_value]
    exact (MeasuredSparsestDistances.vertex_bounds A w (P.get j) fits).1
  have chosen := select_charge (tabulate cells).1 shaped
  exact Nat.add_le_add paid chosen

theorem vertex_threshold_fits (A : Adjacency n) (w : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    {B : ℕ} (fits : ∀ j, StoredBounded (w.get j) B) {i : Fin m} {q : Code}
    (found : (vertex A w P).1 = .threshold i q) : q.Bounded (distanceWidth n (max 1 B)) := by
  let cells := fun j : Fin m => MeasuredSparsestDistances.vertex A w (P.get j)
  have shaped (j : Fin m) : OptionFits (tabulate cells).1[j.val] (distanceWidth n (max 1 B)) := by
    rw [tabulate_value]
    exact (MeasuredSparsestDistances.vertex_bounds A w (P.get j) fits).1
  exact select_threshold_fits (tabulate cells).1 shaped found

end DirectedFlowCutGap.MeasuredSparsestThreshold
