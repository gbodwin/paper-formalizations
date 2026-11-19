import DirectedFlowCutGap.PhysicalEdgeSolver

/-!
# Size of the serialized line graph

This supplies a polynomial in the original edge input dimensions and
rational field width for the source sent to the physical dispatcher.
-/

namespace DirectedFlowCutGap.PhysicalSourceSizeBounds

open BinaryArithmetic

private theorem table_length (rows : List (Bits × Bits)) :
    (SourceRowTableProgram.encode rows).length =
      2 * SourceRowTableProgram.bits rows + 3 * rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨a, b⟩
    simp only [SourceRowTableProgram.encode, SourceRowTableProgram.bits, List.length_cons,
      List.length_append, SelfDelimitedWordProgram.encode_length, ih]
    omega

private theorem table_bits (rows : List (Bits × Bits)) :
    SourceRowTableProgram.bits rows = (rows.map (fun (a, b) => a.length + b.length)).sum := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨a, b⟩
    simp only [SourceRowTableProgram.bits, List.map_cons, List.sum_cons, ih]

def sourceSizeBound (n demands stored : ℕ) : ℕ :=
  2 * (stored + n * n + demands * (n + n)) + 3 * (n + n + demands) + 3

theorem source_size_le {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    (PhysicalSourceDispatch.input D).length ≤ sourceSizeBound n D.demands.length
      (LambdaRowProgram.rowBits D.costs.toList) := by
  let c := SourcePacking.capacityFields D.costs
  let m := SourcePacking.matrixFields D.adjacency
  let d := SourcePacking.demandFields D.demands
  have hc : c.length = n := by simp [c, SourcePacking.capacityFields, IndexedRationalRead.fields]
  have hm : m.length = n := by
    simpa [m, SourcePacking.matrixFields] using GraphRelaxationRefinement.matrix_length D.adjacency
  have hd : d.length = D.demands.length := by simp [d, SourcePacking.demandFields]
  have hcs : SourceRowTableProgram.bits c = LambdaRowProgram.rowBits D.costs.toList :=
    FinalDispatchEnvelope.fields_bits _
  have hms : SourceRowTableProgram.bits m ≤ n * n := by
    rw [table_bits]
    have h := FinalDispatchEnvelope.matrix_cells D.adjacency (N := n) le_rfl
    simpa only [m, SourcePacking.matrixFields, List.map_map, Function.comp_def, List.length_nil,
      Nat.add_zero] using h
  have hds : SourceRowTableProgram.bits d ≤ D.demands.length * (n + n) := by
    rw [table_bits]
    have hh := FinalDispatchEnvelope.sum_map_le d
      (fun (a, b) => a.length + b.length) (n + n) (by
        intro p hp
        change p ∈ D.demands.map _ at hp
        obtain ⟨⟨s, t⟩, _, rfl⟩ := List.mem_map.mp hp
        exact Nat.add_le_add (RowVertices.label_width s) (RowVertices.label_width t))
    simpa only [hd] using hh
  change (PackingSourceInput.encode c m d).length ≤ _
  simp only [PackingSourceInput.encode, List.length_append, table_length, hcs, hc, hm, hd, sourceSizeBound]
  omega

def lineSourceSizeBound (n demands B : ℕ) : ℕ :=
  let m := EncodedEdgeLineInput.lineSize n
  sourceSizeBound m demands (PhysicalEdgeSolver.lineInputSizeBound n demands B)

theorem line_source_size_le {n B : ℕ} (D : EncodedEdgeLineInput.Input n) (hB : 1 ≤ B)
    (hc : ∀ u v : Fin n, (D.costs[u.val][v.val]).num.size ≤ B ∧ (D.costs[u.val][v.val]).den.size ≤ B) :
    (PhysicalSourceDispatch.input (PhysicalEdgeSolver.binaryLineInput D)).length ≤
      lineSourceSizeBound n D.demands.length B := by
  let line := PhysicalEdgeSolver.binaryLineInput D
  have hs := PhysicalEdgeSolver.line_size_le D hB hc
  have hd : line.demands.length = D.demands.length := by
    simp [line, PhysicalEdgeSolver.binaryLineInput, EncodedEdgeLineInput.lineInput]
  have hrows : LambdaRowProgram.rowBits line.costs.toList ≤
      PhysicalEdgeSolver.lineInputSizeBound n D.demands.length B := by
    change OriginalStoreInitial.inputSize line.costs line.demands ≤ _ at hs
    unfold OriginalStoreInitial.inputSize at hs
    omega
  refine (source_size_le line).trans ?_
  change sourceSizeBound _ line.demands.length _ ≤ _
  rw [hd]
  unfold lineSourceSizeBound sourceSizeBound
  dsimp only
  omega

end DirectedFlowCutGap.PhysicalSourceSizeBounds
