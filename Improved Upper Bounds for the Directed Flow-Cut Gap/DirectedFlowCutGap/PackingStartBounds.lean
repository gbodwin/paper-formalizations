import DirectedFlowCutGap.PackingStartExecution

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

def initialWidth (B : ℕ) : ℕ := B+B+1
def bestWidth (n B : ℕ) : ℕ :=
  let S := NormalizedRow.scalarWidth n (initialWidth B)
  S+S+1

def instructionBound (d n B : ℕ) : ℕ :=
  ScalarQuotientRow.instructionBound n B+
    GraphOracleMachine.instructionBound d n (initialWidth B)+
    NormalizedRow.instructionBound n (initialWidth B)+
    ObjectiveRow.instructionBound n (bestWidth n B)+5*n+64

theorem initial_width {n : ℕ} (capacity : Row n) (delta : Fraction) (B : ℕ)
    (hb : StoredBounded delta B) (row : ∀ x∈capacity.toList,StoredBounded x B) :
    ∀ x∈(initial capacity delta).1.toList,StoredBounded x (initialWidth B) := by
  rw [←ScalarQuotientRow.result_eq_initial]
  exact ScalarQuotientRow.result_width true delta capacity.toList B hb row

theorem best_width {n : ℕ} (y : Row n) (mask : Vector Bool n) (U : ℕ)
    (row : ∀ x∈y.toList,StoredBounded x U) :
    ∀ x∈(normalized y mask).1.toList,
      StoredBounded x (NormalizedRow.scalarWidth n U+NormalizedRow.scalarWidth n U+1) := by
  have scalar := NormalizedRow.alpha_width y.toList mask.toList U (by simp) row
  simp only [Vector.length_toList] at scalar
  have small : U≤NormalizedRow.scalarWidth n U := by unfold NormalizedRow.scalarWidth;nlinarith
  have scaled : ∀ x∈y.toList,StoredBounded x (NormalizedRow.scalarWidth n U) :=
    fun x hx => ⟨(row x hx).1.trans small,(row x hx).2.trans small⟩
  have out := ScalarQuotientRow.result_width false (NormalizedRow.alpha y.toList mask.toList)
    y.toList (NormalizedRow.scalarWidth n U) scalar scaled
  rw [←NormalizedRow.result_eq_normalized]
  exact out

theorem start_steps_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (delta : Fraction) (label : Fin n → Bits) (hn : 0<n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (ot B : ℕ) (hB : 1≤B)
    (labels : ∀ i,(label i).length≤B) (scalar : StoredBounded delta B)
    (row : ∀ x∈capacity.toList,StoredBounded x B)
    (ob : ∀ W,1≤W → (∀ i,(label i).length≤W) →
      (∀ x∈(initial capacity delta).1.toList,StoredBounded x W) →
      (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
      ot≤GraphOracleMachine.instructionBound ds.length n W+1) :
    ScalarQuotientRow.steps true delta capacity.toList+ot+25+
      finishSteps capacity (initial capacity delta).1
        (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn (initial capacity delta).1).1
      ≤ instructionBound ds.length n B := by
  let y := (initial capacity delta).1
  let q := (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn y).1
  have small : B ≤ initialWidth B := by unfold initialWidth;omega
  have yi := initial_width capacity delta B scalar row
  have ci : ∀ i,StoredBounded (get capacity i) B := by
    intro i
    apply row
    rw [ScalarQuotientRow.row_toList]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have ho := ob (initialWidth B) (hB.trans small) (fun i => (labels i).trans small) yi
    (fun i => ⟨(ci i).1.trans small,(ci i).2.trans small⟩)
  have hi := ScalarQuotientRow.steps_bound true delta capacity.toList B scalar row
  have hb := best_width y q.mask (initialWidth B) yi
  have scale : B≤bestWidth n B := by unfold bestWidth NormalizedRow.scalarWidth initialWidth;nlinarith
  have hnrm := NormalizedRow.steps_bound y.toList q.mask.toList (initialWidth B) (by simp) yi
  have hobj := ObjectiveRow.steps_bound capacity.toList (normalized y q.mask).1.toList
    (bestWidth n B) (by simp) (fun x hx => ⟨(row x hx).1.trans scale,(row x hx).2.trans scale⟩) hb
  simp only [Vector.length_toList] at hi hnrm hobj
  dsimp only [finishSteps,instructionBound]
  dsimp only [y,q] at hnrm hobj
  omega
end DirectedFlowCutGap.PackingStart
