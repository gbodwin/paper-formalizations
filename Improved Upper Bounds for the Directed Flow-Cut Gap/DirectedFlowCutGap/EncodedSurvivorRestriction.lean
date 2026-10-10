import DirectedFlowCutGap.EncodedShortcutMatrixBridge
import DirectedFlowCutGap.EncodedSurvivorExec
import DirectedFlowCutGap.EncodedUnitCostPreparation

/-!
# Fixed restriction of a retained shortcut matrix to retained survivors

These bodies consume the actual stored shortcut matrix and the actual ordered
survivor words. Each output cell executes the already certified two-read flag
body, including copying the selected row and cell. Fixed row/matrix recursion
adds only its own branches and constructors. There is no callback parameter,
native finite enumeration, runtime decode/map conversion, or second execution
of the mathematical shortcut materializer.

The relation below preserves survivor order and allows arbitrary stored label
padding. Its finite arrays and `build` expressions are proof-side observations.
A producer theorem derives the input relation from the earlier concrete
shortcut-matrix and survivor-scan results. Thus the relation does not assume
an unspecified algorithm. The exact result and output-size laws cover arbitrary
malformed Values; polynomial charge laws require the stated represented input
shape and stored word bounds.

This module gathers adjacency only. Producing the survivor dimension word,
gathering clipped weights and original costs, input representation construction,
replica/chain assembly and the shared reference-model simulation remain separate
joins. The retained port list is borrowed, and its bytes are unchanged.
-/
namespace DirectedFlowCutGap.EncodedSurvivorRestriction
open BinaryArithmetic EncodedSequenceAccess EncodedRestrictedTestExec

def row (table : Value) (source : Bits) : List Bits → Option Value × ℕ
  | [] => (some .empty,1)
  | target::targets =>
      let a := EncodedCellAccess.flag source target table
      match a.1 with
      | none => (none,a.2+4)
      | some b =>
          let r := row table source targets
          match r.1 with
          | none => (none,a.2+r.2+8)
          | some tail => (some (.pair (.flag b) tail),a.2+r.2+12)

inductive RowExec (table : Value) (source : Bits) :
    List Bits → Option Value → ℕ → Prop
  | nil : RowExec table source [] (some .empty) 1
  | missingCell (target : Bits) (targets : List Bits) (q : ℕ) :
      FlagCellExec source target table none q →
      RowExec table source (target::targets) none (q+4)
  | missingTail (target : Bits) (targets : List Bits) (b : Bool) (q r : ℕ) :
      FlagCellExec source target table (some b) q →
      RowExec table source targets none r →
      RowExec table source (target::targets) none (q+r+8)
  | cell (target : Bits) (targets : List Bits) (b : Bool) (tail : Value) (q r : ℕ) :
      FlagCellExec source target table (some b) q →
      RowExec table source targets (some tail) r →
      RowExec table source (target::targets) (some (.pair (.flag b) tail)) (q+r+12)

theorem RowExec.result {table : Value} {source : Bits}
    {targets : List Bits} {out : Option Value} {q : ℕ}
    (h : RowExec table source targets out q) :
    out=(row table source targets).1 ∧ q=(row table source targets).2 := by
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

theorem row_exec (table : Value) (source : Bits) (targets : List Bits) :
    RowExec table source targets
      (row table source targets).1 (row table source targets).2 := by
  induction targets with
  | nil => exact .nil
  | cons target targets ih =>
      have ha := flagCell_exec source target table
      cases hc : (EncodedCellAccess.flag source target table).1 with
      | none =>
          rw [hc] at ha
          simpa only [row,hc] using RowExec.missingCell target targets _ ha
      | some b =>
          rw [hc] at ha
          cases ht : (row table source targets).1 with
          | none =>
              rw [ht] at ih
              simpa only [row,hc,ht] using RowExec.missingTail target targets b _ _ ha ih
          | some tail =>
              rw [ht] at ih
              simpa only [row,hc,ht] using RowExec.cell target targets b tail _ _ ha ih

def matrix (table : Value) (targets : List Bits) :
    List Bits → Option Value × ℕ
  | [] => (some .empty,1)
  | source::sources =>
      let a := row table source targets
      match a.1 with
      | none => (none,a.2+4)
      | some cells =>
          let r := matrix table targets sources
          match r.1 with
          | none => (none,a.2+r.2+8)
          | some tail => (some (.pair cells tail),a.2+r.2+12)

inductive MatrixExec (table : Value) (targets : List Bits) :
    List Bits → Option Value → ℕ → Prop
  | nil : MatrixExec table targets [] (some .empty) 1
  | missingRow (source : Bits) (sources : List Bits) (q : ℕ) :
      RowExec table source targets none q →
      MatrixExec table targets (source::sources) none (q+4)
  | missingTail (source : Bits) (sources : List Bits) (cells : Value) (q r : ℕ) :
      RowExec table source targets (some cells) q →
      MatrixExec table targets sources none r →
      MatrixExec table targets (source::sources) none (q+r+8)
  | row (source : Bits) (sources : List Bits) (cells tail : Value) (q r : ℕ) :
      RowExec table source targets (some cells) q →
      MatrixExec table targets sources (some tail) r →
      MatrixExec table targets (source::sources) (some (.pair cells tail)) (q+r+12)

theorem MatrixExec.result {table : Value} {targets sources : List Bits}
    {out : Option Value} {q : ℕ} (h : MatrixExec table targets sources out q) :
    out=(matrix table targets sources).1 ∧
      q=(matrix table targets sources).2 := by
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

theorem matrix_exec (table : Value) (targets sources : List Bits) :
    MatrixExec table targets sources
      (matrix table targets sources).1 (matrix table targets sources).2 := by
  induction sources with
  | nil => exact .nil
  | cons source sources ih =>
      have ha := row_exec table source targets
      cases hc : (row table source targets).1 with
      | none =>
          rw [hc] at ha
          simpa only [matrix,hc] using MatrixExec.missingRow source sources _ ha
      | some cells =>
          rw [hc] at ha
          cases ht : (matrix table targets sources).1 with
          | none =>
              rw [ht] at ih
              simpa only [matrix,hc,ht] using MatrixExec.missingTail source sources cells _ _ ha ih
          | some tail =>
              rw [ht] at ih
              simpa only [matrix,hc,ht] using MatrixExec.row source sources cells tail _ _ ha ih

/-- Exact order and numeric labels, allowing the actual word padding to vary. -/
def LabelsRepresent {m : ℕ} (words : List Bits) (ports : List (Fin m)) : Prop :=
  List.Forall₂ (fun word port => value word=port.val) words ports

theorem labelsRepresent_encode {m : ℕ} (ports : List (Fin m)) (encode : Fin m → Bits)
    (he : ∀ i, value (encode i)=i.val) : LabelsRepresent (ports.map encode) ports := by
  induction ports with
  | nil => exact .nil
  | cons p ps ih => exact .cons (he p) ih

/-- These finite Value descriptions are observations, not executable producers. -/
def rowValue {m : ℕ} (A : Vector (Vector Bool m) m) (source : Fin m)
    (targets : List (Fin m)) : Value :=
  EncodedSequenceAccess.sequence (targets.map fun target => .flag A[source.val][target.val])

def matrixValue {m : ℕ} (A : Vector (Vector Bool m) m)
    (sources targets : List (Fin m)) : Value :=
  EncodedSequenceAccess.sequence (sources.map fun source => rowValue A source targets)

theorem row_refines {m : ℕ} (A : Vector (Vector Bool m) m)
    (source : Bits) (i : Fin m) (hi : value source=i.val)
    {targets : List Bits} {ports : List (Fin m)} (h : LabelsRepresent targets ports) :
    (row (EncodedCellAccess.flagTable A) source targets).1=some (rowValue A i ports) := by
  induction h with
  | nil => rfl
  | @cons word port words ports hv hr ih =>
      have hc := EncodedCellAccess.flag_get A i port source word hi hv
      simp only [row,hc,ih,rowValue,List.map_cons,EncodedSequenceAccess.sequence]

theorem matrix_refines {m : ℕ} (A : Vector (Vector Bool m) m)
    {sources targets : List Bits} {ss ts : List (Fin m)}
    (hs : LabelsRepresent sources ss) (ht : LabelsRepresent targets ts) :
    (matrix (EncodedCellAccess.flagTable A) targets sources).1=some (matrixValue A ss ts) := by
  induction hs with
  | nil => rfl
  | @cons word port words ports hv hr ih =>
      have hc := row_refines A word port hv ht
      simp only [matrix,hc,ih,matrixValue,List.map_cons,EncodedSequenceAccess.sequence]

def rowBound (m I columns : ℕ) : ℕ := columns*(read2Bound m m I 2+16)+1

def matrixBound (m I rows columns : ℕ) : ℕ := rows*(rowBound m I columns+12)+1

/-- All branches are covered inside the represented Boolean-table shape.
An arbitrary malformed Value needs its own stored-size premise instead. -/
theorem row_bound {m : ℕ} (A : Vector (Vector Bool m) m) (source : Bits)
    (targets : List Bits) (I : ℕ) (hs : source.length ≤ I)
    (ht : ∀ b∈targets, b.length ≤ I) :
    (row (EncodedCellAccess.flagTable A) source targets).2 ≤ rowBound m I targets.length := by
  induction targets with
  | nil => simp [row,rowBound]
  | cons target targets ih =>
      have hc := EncodedCellAccess.flag_bound A source target I hs (ht target (by simp))
      have hr := ih (fun b hb => ht b (by simp [hb]))
      simp only [row,List.length_cons]
      cases hh : (EncodedCellAccess.flag source target (EncodedCellAccess.flagTable A)).1 with
      | none => simp only; unfold rowBound at *; nlinarith
      | some b =>
          cases htail : (row (EncodedCellAccess.flagTable A) source targets).1 <;>
            simp only <;> unfold rowBound at * <;> nlinarith

theorem matrix_bound {m : ℕ} (A : Vector (Vector Bool m) m)
    (targets sources : List Bits) (I : ℕ)
    (ht : ∀ b∈targets, b.length ≤ I) (hs : ∀ b∈sources, b.length ≤ I) :
    (matrix (EncodedCellAccess.flagTable A) targets sources).2 ≤ 
      matrixBound m I sources.length targets.length := by
  induction sources with
  | nil => simp [matrix,matrixBound]
  | cons source sources ih =>
      have hc := row_bound A source targets I (hs source (by simp)) ht
      have hr := ih (fun b hb => hs b (by simp [hb]))
      simp only [matrix,List.length_cons]
      cases hh : (row (EncodedCellAccess.flagTable A) source targets).1 with
      | none => simp only; unfold matrixBound at *; nlinarith
      | some cells =>
          cases htail : (matrix (EncodedCellAccess.flagTable A) targets sources).1 <;>
            simp only <;> unfold matrixBound at * <;> nlinarith

theorem RowExec.cost {m : ℕ} (A : Vector (Vector Bool m) m)
    {source : Bits} {targets : List Bits} {out : Option Value} {q : ℕ}
    (run : RowExec (EncodedCellAccess.flagTable A) source targets out q)
    (I : ℕ) (hs : source.length ≤ I) (ht : ∀ b∈targets, b.length ≤ I) :
    q ≤ rowBound m I targets.length := by
  rw [run.result.2]
  exact row_bound A source targets I hs ht

theorem MatrixExec.cost {m : ℕ} (A : Vector (Vector Bool m) m)
    {sources targets : List Bits} {out : Option Value} {q : ℕ}
    (run : MatrixExec (EncodedCellAccess.flagTable A) targets sources out q)
    (I : ℕ) (ht : ∀ b∈targets, b.length ≤ I) (hs : ∀ b∈sources, b.length ≤ I) :
    q ≤ matrixBound m I sources.length targets.length := by
  rw [run.result.2]
  exact matrix_bound A targets sources I ht hs

/-- Exact result shapes are unconditional on the input Value's shape. -/
theorem row_size (table : Value) (source : Bits) (targets : List Bits)
    (out : Value) (hout : (row table source targets).1=some out) :
    out.size ≤ 3*targets.length+1 := by
  induction targets generalizing out with
  | nil => simp only [row,Option.some.injEq] at hout; subst out; simp [Value.size]
  | cons target targets ih =>
      cases hc : (EncodedCellAccess.flag source target table).1 with
      | none => simp [row,hc] at hout
      | some b =>
          cases ht : (row table source targets).1 with
          | none => simp [row,hc,ht] at hout
          | some tail =>
              have hb := ih tail ht
              simp only [row,hc,ht,Option.some.injEq] at hout
              subst out
              simp only [Value.size,List.length_cons]
              omega

theorem matrix_size (table : Value) (targets sources : List Bits)
    (out : Value) (hout : (matrix table targets sources).1=some out) :
    out.size ≤ sources.length*(3*targets.length+2)+1 := by
  induction sources generalizing out with
  | nil => simp only [matrix,Option.some.injEq] at hout; subst out; simp [Value.size]
  | cons source sources ih =>
      cases hc : (row table source targets).1 with
      | none => simp [matrix,hc] at hout
      | some cells =>
          cases ht : (matrix table targets sources).1 with
          | none => simp [matrix,hc,ht] at hout
          | some tail =>
              have hb := ih tail ht
              have ha := row_size table source targets cells hc
              simp only [matrix,hc,ht,Option.some.injEq] at hout
              subst out
              simp only [Value.size,List.length_cons]
              nlinarith

/-- The caller retains the same label bytes; no conversion or regeneration occurs. -/
structure Output where
  ports : List Bits
  adjacency : Option Value
  operations : ℕ
  deriving DecidableEq, Repr

def restrict (table : Value) (survivors : List Bits) : Output :=
  let r := matrix table survivors survivors
  ⟨survivors,r.1,r.2+4⟩

inductive RestrictExec (table : Value) (survivors : List Bits) : Output → Prop
  | make (out : Option Value) (q : ℕ) : MatrixExec table survivors survivors out q →
      RestrictExec table survivors ⟨survivors,out,q+4⟩

theorem restrict_exec (table : Value) (survivors : List Bits) :
    RestrictExec table survivors (restrict table survivors) :=
  .make _ _ (matrix_exec table survivors survivors)

theorem RestrictExec.result {table : Value} {survivors : List Bits} {out : Output}
    (run : RestrictExec table survivors out) : out=restrict table survivors := by
  cases run with
  | make out q h =>
      have hh := h.result
      simp only [restrict,← hh.1,← hh.2]

@[simp] theorem restrict_ports (table : Value) (survivors : List Bits) :
    (restrict table survivors).ports=survivors := rfl

theorem restrict_bound {m : ℕ} (A : Vector (Vector Bool m) m) (survivors : List Bits)
    (I : ℕ) (hw : ∀ b∈survivors, b.length ≤ I) :
    (restrict (EncodedCellAccess.flagTable A) survivors).operations ≤ 
      matrixBound m I survivors.length survivors.length+4 :=
  Nat.add_le_add_right (matrix_bound A survivors survivors I hw hw) 4

theorem restrict_size (table : Value) (survivors : List Bits) (out : Value)
    (h : (restrict table survivors).adjacency=some out) :
    out.size ≤ survivors.length*(3*survivors.length+2)+1 :=
  matrix_size table survivors survivors out h

private theorem vector_list {α : Type*} {m : ℕ} (v : Vector α m) :
    v.toList=(List.finRange m).map (fun i => v[i.val]) := by
  simpa only [Vector.toList_ofFn,List.finRange,List.map_ofFn,Function.comp_def] using
    congrArg Vector.toList (Vector.ofFn_getElem (xs := v)).symm

/-- The mathematical submatrix agrees with the existing stored prepared graph. -/
theorem prepared_matrixValue {n : ℕ} (D : EncodedUnitCostReplication.Input n) :
    matrixValue (EncodedPortPreparation.portData D).materialize.adjacency
      (EncodedUnitCostPreparation.build D).ports.toList
      (EncodedUnitCostPreparation.build D).ports.toList =
      EncodedCellAccess.flagTable (EncodedUnitCostPreparation.build D).data.adjacency := by
  unfold matrixValue EncodedCellAccess.flagTable
  rw [vector_list (EncodedUnitCostPreparation.build D).ports,
    vector_list (EncodedUnitCostPreparation.build D).data.adjacency]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  unfold rowValue
  rw [vector_list (EncodedUnitCostPreparation.build D).data.adjacency[i.val]]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp only [EncodedUnitCostPreparation.build,Vector.getElem_ofFn]

/-- A representation relation on the actual values delivered by concrete producers. -/
structure PreparationInputs {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (shortcutMatrix : Value) (survivors : List Bits) : Prop where
  matrix_eq : shortcutMatrix=
    EncodedCellAccess.flagTable (EncodedPortPreparation.portData D).materialize.adjacency
  labels : LabelsRepresent survivors (EncodedUnitCostPreparation.build D).ports.toList

structure PreparedAdjacency {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (out : Output) : Prop where
  ports : LabelsRepresent out.ports (EncodedUnitCostPreparation.build D).ports.toList
  adjacency : out.adjacency=
    some (EncodedCellAccess.flagTable (EncodedUnitCostPreparation.build D).data.adjacency)

theorem restrict_prepared {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (shortcutMatrix : Value) (survivors : List Bits)
    (h : PreparationInputs D shortcutMatrix survivors) :
    PreparedAdjacency D (restrict shortcutMatrix survivors) := by
  refine ⟨h.labels,?_⟩
  change (matrix shortcutMatrix survivors survivors).1=_
  rw [h.matrix_eq]
  exact (matrix_refines (EncodedPortPreparation.portData D).materialize.adjacency
    h.labels h.labels).trans (congrArg some (prepared_matrixValue D))

theorem prepared_ports_list {n : ℕ} (D : EncodedUnitCostReplication.Input n) :
    (EncodedUnitCostPreparation.build D).ports.toList=
      (RetainedSurvivorEnumeration.labels (EncodedPortPreparation.portData D).removed).map Subtype.val := by
  simp [EncodedUnitCostPreparation.build,RetainedSurvivorEnumeration.labels]

/-- Both witnesses describe outputs of the earlier fixed programs on the same
retained enumeration. No producer is assumed abstractly and no materializer is rerun. -/
theorem inputs_of_produced {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (encode : Fin (3*n) → Bits) (he : ∀ i, value (encode i)=i.val)
    (all : List Bits) (hall : all=(List.finRange (3*n)).map encode)
    (shortcutMatrix : Value) (survivors : List Bits)
    (hm : (EncodedShortcutMatrixExec.matrix
      (EncodedCellAccess.flagTable (EncodedPortPreparation.portData D).adjacency)
      (maskValue (EncodedPortPreparation.portData D).removed) all all all).1=some shortcutMatrix)
    (hs : (EncodedSurvivorExec.scan (maskValue (EncodedPortPreparation.portData D).removed) all).1=
      some survivors) : PreparationInputs D shortcutMatrix survivors := by
  subst all
  have hmatrix := EncodedShortcutMatrixBridge.materialize_refines
    (EncodedPortPreparation.portData D) encode he
  have hscan := EncodedSurvivorExec.scan_refines
    (EncodedPortPreparation.portData D).removed encode he (List.finRange (3*n))
  rw [hm] at hmatrix
  rw [hs] at hscan
  refine ⟨Option.some.inj hmatrix,?_⟩
  have hlabels := Option.some.inj hscan
  rw [hlabels,prepared_ports_list D]
  change LabelsRepresent
    ((RetainedSurvivorEnumeration.labels (EncodedPortPreparation.portData D).removed).map
      (fun v => encode v.val))
    ((RetainedSurvivorEnumeration.labels (EncodedPortPreparation.portData D).removed).map Subtype.val)
  have hh := labelsRepresent_encode
    ((RetainedSurvivorEnumeration.labels (EncodedPortPreparation.portData D).removed).map Subtype.val)
    encode he
  simpa only [List.map_map,Function.comp_def] using hh

theorem restrict_produced {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (encode : Fin (3*n) → Bits) (he : ∀ i, value (encode i)=i.val)
    (all : List Bits) (hall : all=(List.finRange (3*n)).map encode)
    (shortcutMatrix : Value) (survivors : List Bits)
    (hm : (EncodedShortcutMatrixExec.matrix
      (EncodedCellAccess.flagTable (EncodedPortPreparation.portData D).adjacency)
      (maskValue (EncodedPortPreparation.portData D).removed) all all all).1=some shortcutMatrix)
    (hs : (EncodedSurvivorExec.scan (maskValue (EncodedPortPreparation.portData D).removed) all).1=
      some survivors) : PreparedAdjacency D (restrict shortcutMatrix survivors) :=
  restrict_prepared D shortcutMatrix survivors (inputs_of_produced D encode he all hall shortcutMatrix survivors hm hs)

theorem PreparationInputs.length {n : ℕ} {D : EncodedUnitCostReplication.Input n}
    {shortcutMatrix : Value} {survivors : List Bits}
    (h : PreparationInputs D shortcutMatrix survivors) :
    survivors.length=(EncodedUnitCostPreparation.build D).size := by
  exact (List.Forall₂.length_eq h.labels).trans
    (Vector.length_toList (xs := (EncodedUnitCostPreparation.build D).ports))

/-- Original n supplies the numerical traversal bound, independently of padding. -/
theorem restrict_prepared_bound {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (shortcutMatrix : Value) (survivors : List Bits)
    (h : PreparationInputs D shortcutMatrix survivors)
    (I : ℕ) (hw : ∀ b∈survivors, b.length ≤ I) :
    (restrict shortcutMatrix survivors).operations ≤ matrixBound (3*n) I (3*n) (3*n)+4 := by
  have hl : survivors.length ≤ 3*n := h.length.trans_le (EncodedUnitCostPreparation.build_size_le D)
  rw [h.matrix_eq]
  apply (restrict_bound (EncodedPortPreparation.portData D).materialize.adjacency survivors I hw).trans
  unfold matrixBound rowBound
  gcongr

/-- The actual successful filter output inherits its stored-word bounds. -/
theorem survivor_widths (removed : Value) (all survivors : List Bits) (I : ℕ)
    (hw : ∀ b∈all, b.length ≤ I) (hs : (EncodedSurvivorExec.scan removed all).1=some survivors) :
    survivors.length ≤ all.length ∧ ∀ b∈survivors, b.length ≤ I := by
  have h := EncodedSurvivorExec.scan_shape removed all survivors hs
  exact ⟨h.1,fun b hb => hw b (h.2 b hb)⟩

theorem restrict_prepared_size {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (shortcutMatrix : Value) (survivors : List Bits)
    (h : PreparationInputs D shortcutMatrix survivors) (out : Value)
    (hout : (restrict shortcutMatrix survivors).adjacency=some out) :
    out.size ≤ (3*n)*(9*n+2)+1 := by
  have hl : survivors.length ≤ 3*n := h.length.trans_le (EncodedUnitCostPreparation.build_size_le D)
  have hs := restrict_size shortcutMatrix survivors out hout
  apply hs.trans
  calc
    survivors.length*(3*survivors.length+2)+1 ≤ (3*n)*(3*(3*n)+2)+1 := by gcongr
    _=(3*n)*(9*n+2)+1 := by ring

end DirectedFlowCutGap.EncodedSurvivorRestriction
