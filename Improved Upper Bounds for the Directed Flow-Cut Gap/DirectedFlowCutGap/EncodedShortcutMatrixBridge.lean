import DirectedFlowCutGap.EncodedShortcutMatrixExec

/-!
# Exact native-table bridge for the closed shortcut materializer

The output of the fixed binary-label loops is exactly the stored flag-table
representation used by the existing weighted preparation. This equality is an
observation of the produced value, not an executable conversion pass. The
retained label enumeration and original adjacency/removal values are inputs.
-/
namespace DirectedFlowCutGap.EncodedShortcutMatrixBridge
open BinaryArithmetic EncodedSequenceAccess EncodedShortcutMatrixExec
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

private theorem vector_list {α : Type*} {m : ℕ} (v : Vector α m) :
    v.toList=(List.finRange m).map (fun i => v[i.val]) := by
  simpa only [Vector.toList_ofFn,List.finRange,List.map_ofFn,Function.comp_def] using
    congrArg Vector.toList (Vector.ofFn_getElem (xs := v)).symm

private theorem standard_vertices (m : ℕ) :
    (ResidualSearch.Enumeration.fin m).vertices = List.finRange m := by
  change List.ofFn (Equiv.refl (Fin m) : Fin m → Fin m) =
    List.ofFn (fun i : Fin m => i)
  apply congrArg List.ofFn
  funext i
  rfl

variable {m : ℕ} (D : EncodedShortcutReachability.Input m)

/-- The search dictionary can change implementation witnesses but cannot
change the computed shortcut flag. Both directions use the real path theorem. -/
theorem shortcut_cell (E : ResidualSearch.Enumeration (Fin m)) (s t : Fin m) :
    (D.shortcut E (Fin.fintype m) s t).1=D.materialize.adjacency[s.val][t.val] := by
  rw [D.materialize_cell]
  apply Bool.eq_iff_iff.mpr
  exact (D.shortcut_true E (Fin.fintype m) s t).trans
    (D.shortcut_true (ResidualSearch.Enumeration.fin m)
      (EncodedShortcutReachability.Input.retainedDictionary
        (ResidualSearch.Enumeration.fin m)) s t).symm

theorem matrixValue_native (E : ResidualSearch.Enumeration (Fin m)) :
    matrixValue D E (List.finRange m) (List.finRange m) =
      EncodedCellAccess.flagTable D.materialize.adjacency := by
  unfold matrixValue EncodedCellAccess.flagTable
  rw [vector_list D.materialize.adjacency]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro s hs
  unfold rowValue
  rw [vector_list D.materialize.adjacency[s.val]]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  exact congrArg Value.flag (shortcut_cell D E s t)

theorem materialize_refines (encode : Fin m → Bits) (he : ∀ v, value (encode v)=v.val) :
    (matrix (EncodedCellAccess.flagTable D.adjacency)
      (EncodedRestrictedTestExec.maskValue D.removed)
      ((List.finRange m).map encode) ((List.finRange m).map encode)
      ((List.finRange m).map encode)).1 =
        some (EncodedCellAccess.flagTable D.materialize.adjacency) := by
  have h := matrix_refines D encode he (ResidualSearch.Enumeration.fin m)
    (List.finRange m) (List.finRange m)
  rw [matrixValue_native D,standard_vertices] at h
  exact h

theorem materialize_bound (encode : Fin m → Bits) (he : ∀ v, value (encode v)=v.val)
    (B : ℕ) (hw : ∀ v, (encode v).length ≤ B) :
    (matrix (EncodedCellAccess.flagTable D.adjacency)
      (EncodedRestrictedTestExec.maskValue D.removed)
      ((List.finRange m).map encode) ((List.finRange m).map encode)
      ((List.finRange m).map encode)).2 ≤ matrixBound m B m m := by
  have h := matrix_bound D encode he (ResidualSearch.Enumeration.fin m)
    (List.finRange m) (List.finRange m) B hw
  simpa only [standard_vertices,List.length_finRange] using h

end DirectedFlowCutGap.EncodedShortcutMatrixBridge
