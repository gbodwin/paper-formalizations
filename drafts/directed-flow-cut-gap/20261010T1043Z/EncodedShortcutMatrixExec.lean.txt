import DirectedFlowCutGap.EncodedShortcutExec

/-!
# Fixed stored-value loops for shortcut matrix construction

Each reached cell invokes the closed shortcut program exactly once. Its flag
is held across the tail recursion; the row and outer sequence pair nodes are
assembled on unwind. Only reached malformed reads cause failure. Traversal
uses retained binary vertex labels, with no run-time enumeration oracle,
arbitrary predicate, or native cardinal loop.

The refinement describes the actual materialized flags. The displayed local
charge includes loop control and stored constructors. Input production and
the common argument/frame copying bound are not discharged by this module.
-/
namespace DirectedFlowCutGap.EncodedShortcutMatrixExec
open BinaryArithmetic EncodedSequenceAccess EncodedRootVisitExec EncodedShortcutExec
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

def row (adjacency removed : Value) (vertices : List Bits) (source : Bits) :
    List Bits → Option Value × ℕ
  | [] => (some .empty,1)
  | target::targets =>
      let a := shortcut ⟨source,target,adjacency,removed⟩ vertices
      match a.1 with
      | none => (none,a.2+4)
      | some b =>
          let r := row adjacency removed vertices source targets
          match r.1 with
          | none => (none,a.2+r.2+8)
          | some tail => (some (.pair (.flag b) tail),a.2+r.2+12)

inductive RowExec (adjacency removed : Value) (vertices : List Bits) (source : Bits) :
    List Bits → Option Value → ℕ → Prop
  | nil : RowExec adjacency removed vertices source [] (some .empty) 1
  | missingCell (target : Bits) (targets : List Bits) (q : ℕ) :
      ShortcutExec ⟨source,target,adjacency,removed⟩ vertices none q →
      RowExec adjacency removed vertices source (target::targets) none (q+4)
  | missingTail (target : Bits) (targets : List Bits) (b : Bool) (q r : ℕ) :
      ShortcutExec ⟨source,target,adjacency,removed⟩ vertices (some b) q →
      RowExec adjacency removed vertices source targets none r →
      RowExec adjacency removed vertices source (target::targets) none (q+r+8)
  | cell (target : Bits) (targets : List Bits) (b : Bool) (tail : Value) (q r : ℕ) :
      ShortcutExec ⟨source,target,adjacency,removed⟩ vertices (some b) q →
      RowExec adjacency removed vertices source targets (some tail) r →
      RowExec adjacency removed vertices source (target::targets)
        (some (.pair (.flag b) tail)) (q+r+12)

theorem RowExec.result {adjacency removed : Value} {vertices : List Bits} {source : Bits}
    {targets : List Bits} {out : Option Value} {q : ℕ}
    (h : RowExec adjacency removed vertices source targets out q) :
    out=(row adjacency removed vertices source targets).1 ∧
      q=(row adjacency removed vertices source targets).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | missingCell target targets q ha =>
      have a := ha.result
      constructor <;> simp only [row,← a.1,← a.2]
  | missingTail target targets b q r ha hr ih =>
      have a := ha.result
      constructor <;> simp only [row,← a.1,← a.2,← ih.1,← ih.2]
  | cell target targets b tail q r ha hr ih =>
      have a := ha.result
      constructor <;> simp only [row,← a.1,← a.2,← ih.1,← ih.2]

theorem row_exec (adjacency removed : Value) (vertices : List Bits) (source : Bits)
    (targets : List Bits) :
    RowExec adjacency removed vertices source targets
      (row adjacency removed vertices source targets).1
      (row adjacency removed vertices source targets).2 := by
  induction targets with
  | nil => exact .nil
  | cons target targets ih =>
      have ha := shortcut_exec ⟨source,target,adjacency,removed⟩ vertices
      cases hc : (shortcut ⟨source,target,adjacency,removed⟩ vertices).1 with
      | none =>
          rw [hc] at ha
          simpa only [row,hc] using RowExec.missingCell target targets _ ha
      | some b =>
          rw [hc] at ha
          cases ht : (row adjacency removed vertices source targets).1 with
          | none =>
              rw [ht] at ih
              simpa only [row,hc,ht] using RowExec.missingTail target targets b _ _ ha ih
          | some tail =>
              rw [ht] at ih
              simpa only [row,hc,ht] using RowExec.cell target targets b tail _ _ ha ih

def matrix (adjacency removed : Value) (vertices targets : List Bits) :
    List Bits → Option Value × ℕ
  | [] => (some .empty,1)
  | source::sources =>
      let a := row adjacency removed vertices source targets
      match a.1 with
      | none => (none,a.2+4)
      | some cells =>
          let r := matrix adjacency removed vertices targets sources
          match r.1 with
          | none => (none,a.2+r.2+8)
          | some tail => (some (.pair cells tail),a.2+r.2+12)

inductive MatrixExec (adjacency removed : Value) (vertices targets : List Bits) :
    List Bits → Option Value → ℕ → Prop
  | nil : MatrixExec adjacency removed vertices targets [] (some .empty) 1
  | missingRow (source : Bits) (sources : List Bits) (q : ℕ) :
      RowExec adjacency removed vertices source targets none q →
      MatrixExec adjacency removed vertices targets (source::sources) none (q+4)
  | missingTail (source : Bits) (sources : List Bits) (cells : Value) (q r : ℕ) :
      RowExec adjacency removed vertices source targets (some cells) q →
      MatrixExec adjacency removed vertices targets sources none r →
      MatrixExec adjacency removed vertices targets (source::sources) none (q+r+8)
  | row (source : Bits) (sources : List Bits) (cells tail : Value) (q r : ℕ) :
      RowExec adjacency removed vertices source targets (some cells) q →
      MatrixExec adjacency removed vertices targets sources (some tail) r →
      MatrixExec adjacency removed vertices targets (source::sources)
        (some (.pair cells tail)) (q+r+12)

theorem MatrixExec.result {adjacency removed : Value} {vertices targets sources : List Bits}
    {out : Option Value} {q : ℕ}
    (h : MatrixExec adjacency removed vertices targets sources out q) :
    out=(matrix adjacency removed vertices targets sources).1 ∧
      q=(matrix adjacency removed vertices targets sources).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | missingRow source sources q ha =>
      have a := ha.result
      constructor <;> simp only [matrix,← a.1,← a.2]
  | missingTail source sources cells q r ha hr ih =>
      have a := ha.result
      constructor <;> simp only [matrix,← a.1,← a.2,← ih.1,← ih.2]
  | row source sources cells tail q r ha hr ih =>
      have a := ha.result
      constructor <;> simp only [matrix,← a.1,← a.2,← ih.1,← ih.2]

theorem matrix_exec (adjacency removed : Value) (vertices targets sources : List Bits) :
    MatrixExec adjacency removed vertices targets sources
      (matrix adjacency removed vertices targets sources).1
      (matrix adjacency removed vertices targets sources).2 := by
  induction sources with
  | nil => exact .nil
  | cons source sources ih =>
      have ha := row_exec adjacency removed vertices source targets
      cases hc : (row adjacency removed vertices source targets).1 with
      | none =>
          rw [hc] at ha
          simpa only [matrix,hc] using MatrixExec.missingRow source sources _ ha
      | some cells =>
          rw [hc] at ha
          cases ht : (matrix adjacency removed vertices targets sources).1 with
          | none =>
              rw [ht] at ih
              simpa only [matrix,hc,ht] using MatrixExec.missingTail source sources cells _ _ ha ih
          | some tail =>
              rw [ht] at ih
              simpa only [matrix,hc,ht] using MatrixExec.row source sources cells tail _ _ ha ih

variable {m : ℕ} (D : EncodedShortcutReachability.Input m)
variable (encode : Fin m → Bits) (he : ∀ v, value (encode v)=v.val)
variable (E : ResidualSearch.Enumeration (Fin m))
include he

/-- A representation observation; no function here is an executable callback. -/
def rowValue (source : Fin m) (targets : List (Fin m)) : Value :=
  sequence (targets.map fun t => .flag (D.shortcut E (Fin.fintype m) source t).1)

theorem row_refines (source : Fin m) (targets : List (Fin m)) :
    (row (EncodedCellAccess.flagTable D.adjacency)
      (EncodedRestrictedTestExec.maskValue D.removed) (E.vertices.map encode)
      (encode source) (targets.map encode)).1 = some (rowValue D E source targets) := by
  induction targets with
  | nil => rfl
  | cons target targets ih =>
      have hc := EncodedShortcutExec.shortcut_refines D encode he E source target
      simp only [inputValue] at hc
      simp only [List.map_cons,row,hc,ih,rowValue,EncodedSequenceAccess.sequence]

def matrixValue (sources targets : List (Fin m)) : Value :=
  sequence (sources.map fun s => rowValue D E s targets)

theorem matrix_refines (sources targets : List (Fin m)) :
    (matrix (EncodedCellAccess.flagTable D.adjacency)
      (EncodedRestrictedTestExec.maskValue D.removed) (E.vertices.map encode)
      (targets.map encode) (sources.map encode)).1 = some (matrixValue D E sources targets) := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      simp only [List.map_cons,matrix,row_refines D encode he E,ih,matrixValue,EncodedSequenceAccess.sequence]

def rowBound (m B length : ℕ) : ℕ := length*(shortcutBound m B+12)+1

theorem row_bound (source : Fin m) (targets : List (Fin m)) (B : ℕ)
    (hw : ∀ v, (encode v).length ≤ B) :
    (row (EncodedCellAccess.flagTable D.adjacency)
      (EncodedRestrictedTestExec.maskValue D.removed) (E.vertices.map encode)
      (encode source) (targets.map encode)).2 ≤ rowBound m B targets.length := by
  induction targets with
  | nil => simp [row,rowBound]
  | cons target targets ih =>
      have hc := EncodedShortcutExec.shortcut_refines D encode he E source target
      have hb := EncodedShortcutExec.shortcut_bound D encode he E source target B hw
      have hr := row_refines D encode he E source targets
      simp only [inputValue] at hc hb
      simp only [List.map_cons,List.length_cons,row,hc,hr]
      unfold rowBound at *
      nlinarith

def matrixBound (m B rows columns : ℕ) : ℕ := rows*(rowBound m B columns+12)+1

theorem matrix_bound (sources targets : List (Fin m)) (B : ℕ)
    (hw : ∀ v, (encode v).length ≤ B) :
    (matrix (EncodedCellAccess.flagTable D.adjacency)
      (EncodedRestrictedTestExec.maskValue D.removed) (E.vertices.map encode)
      (targets.map encode) (sources.map encode)).2 ≤
        matrixBound m B sources.length targets.length := by
  induction sources with
  | nil => simp [matrix,matrixBound]
  | cons source sources ih =>
      have hc := row_refines D encode he E source targets
      have hb := row_bound D encode he E source targets B hw
      have hr := matrix_refines D encode he E sources targets
      simp only [List.map_cons,List.length_cons,matrix,hc,hr]
      unfold matrixBound at *
      nlinarith

omit he in
theorem rowValue_size (source : Fin m) (targets : List (Fin m)) :
    (rowValue D E source targets).size ≤ 3*targets.length+1 := by
  have h := sequence_size_bound (xs := targets.map fun t =>
    Value.flag (D.shortcut E (Fin.fintype m) source t).1) (S := 2) (by
      intro x hx
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
      rfl)
  simpa only [rowValue,List.length_map,Nat.mul_comm] using h

omit he in
theorem matrixValue_size (sources targets : List (Fin m)) :
    (matrixValue D E sources targets).size ≤ sources.length*(3*targets.length+2)+1 := by
  have h := sequence_size_bound (xs := sources.map fun s => rowValue D E s targets)
    (S := 3*targets.length+1) (by
      intro x hx
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
      exact rowValue_size D E s targets)
  simpa only [matrixValue,List.length_map,Nat.add_assoc] using h

end DirectedFlowCutGap.EncodedShortcutMatrixExec
