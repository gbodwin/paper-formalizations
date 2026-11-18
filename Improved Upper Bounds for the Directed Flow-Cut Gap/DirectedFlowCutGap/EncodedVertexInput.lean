import DirectedFlowCutGap.EncodedVertexSolver
import DirectedFlowCutGap.BinaryFractionalGuesses
import DirectedFlowCutGap.SourcePackingEncoding

/-!
# Reading the existing source-table encoding into typed vertex input

The three tables use the existing source row and word markers. Decoding
retains the padded cost fields, rejects zero denominators, checks that the
adjacency matrix is square, and checks the original demand endpoints.
-/

namespace DirectedFlowCutGap.EncodedVertexInput

open BinaryArithmetic

def readWord : Bits → Option (Bits × Bits)
  | false :: rest => some ([], rest)
  | true :: b :: rest => (readWord rest).map fun (bits, suffix) => (b :: bits, suffix)
  | _ => none

theorem readWord_prefix (word suffix : Bits) :
    readWord (SelfDelimitedWordProgram.encode word ++ suffix) = some (word, suffix) := by
  induction word with
  | nil => rfl
  | cons b rest ih => simp [SelfDelimitedWordProgram.encode, readWord, ih]

abbrev Row := Bits × Bits
abbrev Table := List Row

def readRows : ℕ → Bits → Option (Table × Bits)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => do
    let (a, rest) ← readWord rest
    let (b, rest) ← readWord rest
    let (rows, suffix) ← readRows fuel rest
    pure ((a, b) :: rows, suffix)

theorem readRows_prefix (rows : Table) (suffix : Bits) (fuel : ℕ) (h : rows.length < fuel) :
    readRows fuel (SourceRowTableProgram.encode rows ++ suffix) = some (rows, suffix) := by
  induction rows generalizing fuel with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | cons row rows ih =>
    rcases row with ⟨a, b⟩
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hf : rows.length < fuel := by simp only [List.length_cons] at h; omega
      simp [SourceRowTableProgram.encode, List.append_assoc, readRows, readWord_prefix, ih fuel hf]

def readTable (bs : Bits) : Option (Table × Bits) := readRows bs.length bs

theorem table_prefix_has_fuel (rows : Table) (suffix : Bits) :
    rows.length < (SourceRowTableProgram.encode rows ++ suffix).length := by
  induction rows with
  | nil => simp [SourceRowTableProgram.encode]
  | cons row rows ih =>
    rcases row with ⟨a, b⟩
    simp only [SourceRowTableProgram.encode, List.cons_append, List.length_cons, List.length_append] at *
    omega

theorem readTable_prefix (rows : Table) (suffix : Bits) :
    readTable (SourceRowTableProgram.encode rows ++ suffix) = some (rows, suffix) :=
  readRows_prefix rows suffix _ (table_prefix_has_fuel rows suffix)

def readTables (source : Bits) : Option (Table × Table × Table × Bits) := do
  let (capacity, rest) ← readTable source
  let (matrix, rest) ← readTable rest
  let (demands, rest) ← readTable rest
  pure (capacity, matrix, demands, rest)

theorem readTables_prefix (capacity matrix demands : Table) (suffix : Bits) :
    readTables (PackingSourceInput.encode capacity matrix demands ++ suffix) =
      some (capacity, matrix, demands, suffix) := by
  simp [PackingSourceInput.encode, readTables, List.append_assoc, readTable_prefix]

def readFraction (row : Row) : Option BinaryRational.Fraction :=
  (BinaryRational.fromBits row.1 row.2).1

def readMatrixRow (n : ℕ) (row : Row) : Option (Vector Bool n) :=
  if h : row.1.length = n ∧ row.2 = [] then
    some ⟨row.1.toArray, by simpa using h.1⟩
  else none

def readDemand (n : ℕ) (row : Row) : Option (Fin n × Fin n) :=
  let a := value row.1
  let b := value row.2
  if h : a < n ∧ b < n then some (⟨a, h.1⟩, ⟨b, h.2⟩) else none

abbrev Input := Σ n, BinaryFractionalGuesses.Input n

private def assembleSized {n : ℕ} (costs : List BinaryRational.Fraction) (hn : costs.length = n)
    (matrix demands : Table) : Option (BinaryFractionalGuesses.Input n) := do
  let matrix ← matrix.mapM (readMatrixRow n)
  let pairs ← demands.mapM (readDemand n)
  if h : matrix.length = n then
    pure ⟨⟨matrix.toArray, by simpa using h⟩, pairs, ⟨costs.toArray, by simpa using hn⟩⟩
  else none

def assemble (capacity matrix demands : Table) : Option Input := do
  let costs ← capacity.mapM readFraction
  (assembleSized costs rfl matrix demands).map fun D => ⟨costs.length, D⟩

def parse (source : Bits) : Option Input := do
  let (capacity, matrix, demands, suffix) ← readTables source
  if suffix.isEmpty then assemble capacity matrix demands else none

theorem parse_wire (capacity matrix demands : Table) :
    parse (PackingSourceInput.encode capacity matrix demands) = assemble capacity matrix demands := by
  have h := readTables_prefix capacity matrix demands []
  simp only [List.append_nil] at h
  simp [parse, h]

theorem mapM_encoded {A B : Type} (encoder : A → B) (decoder : B → Option A) (xs : List A)
    (h : ∀ a, decoder (encoder a) = some a) :
    (xs.map encoder).mapM decoder = some xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [h, ih]

theorem readFraction_fields (r : BinaryRational.Fraction) :
    readFraction (r.num, r.den) = some r := by
  have hz : (isZero r.den).1 ≠ true :=
    fun h => (Nat.ne_of_gt r.den_pos) ((isZero_spec r.den).1.mp h)
  cases r
  simp [readFraction, BinaryRational.fromBits, hz]

theorem readMatrixRow_fields {n : ℕ} (row : Vector Bool n) :
    readMatrixRow n (row.toList, []) = some row := by
  have h : row.toList.length = n ∧ ([] : Bits) = [] := by simp
  rw [readMatrixRow, dite_eq_left h]
  apply congrArg some
  apply Vector.toList_inj.mp
  simp

theorem readDemand_fields {n : ℕ} (d : Fin n × Fin n) :
    readDemand n (RowVertices.vertexLabel d.1, RowVertices.vertexLabel d.2) = some d := by
  obtain ⟨s, t⟩ := d
  simp [readDemand, RowVertices.label_numeric, s.isLt, t.isLt]

theorem assemble_fields {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    assemble (SourcePacking.capacityFields D.costs) (SourcePacking.matrixFields D.adjacency)
      (SourcePacking.demandFields D.demands) = some ⟨n, D⟩ := by
  have hc : (SourcePacking.capacityFields D.costs).mapM readFraction = some D.costs.toList := by
    exact mapM_encoded (fun r => (r.num, r.den)) readFraction _ readFraction_fields
  have hm : (SourcePacking.matrixFields D.adjacency).mapM (readMatrixRow n) =
      some D.adjacency.toList := by
    change ((D.adjacency.toList.map Vector.toList).map (fun row => (row, ([] : Bits)))).mapM _ = _
    rw [List.map_map]
    exact mapM_encoded (fun r => (r.toList, [])) (readMatrixRow n) _ readMatrixRow_fields
  have hd : (SourcePacking.demandFields D.demands).mapM (readDemand n) = some D.demands :=
    mapM_encoded (fun (d : Fin n × Fin n) => (RowVertices.vertexLabel d.1, RowVertices.vertexLabel d.2))
      (readDemand n) D.demands readDemand_fields
  have hn : D.costs.toList.length = n := by simp
  have hs : assembleSized D.costs.toList hn (SourcePacking.matrixFields D.adjacency)
      (SourcePacking.demandFields D.demands) = some D := by
    simp [assembleSized, hm, hd]
    cases D
    rfl
  have lift (m : ℕ) (hmn : D.costs.toList.length = m) (he : m = n) :
      (assembleSized D.costs.toList hmn (SourcePacking.matrixFields D.adjacency)
        (SourcePacking.demandFields D.demands)).map (fun x => (⟨m, x⟩ : Input)) =
          some ⟨n, D⟩ := by
    cases he
    rw [hs]
    rfl
  unfold assemble
  rw [hc]
  exact lift _ rfl hn

theorem parse_encode {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    parse (SourcePacking.encode D.costs D.adjacency D.demands) = some ⟨n, D⟩ := by
  rw [SourcePacking.encode, parse_wire, assemble_fields]

def massBitTree (T : ℕ) (source : Bits) :
    Option (Σ n, FiniteDrawTrees.Tree (EncodedVertexSolver.Output n)) :=
  (parse source).map fun ⟨n, input⟩ =>
    ⟨n, EncodedVertexSolver.massBitTree T (BinaryFractionalGuesses.decodeInput input)⟩

def sizeBitTree (T : ℕ) (source : Bits) :
    Option (Σ n, FiniteDrawTrees.Tree (EncodedVertexSolver.Output n)) :=
  (parse source).map fun ⟨n, input⟩ =>
    ⟨n, EncodedVertexSolver.sizeBitTree T (BinaryFractionalGuesses.decodeInput input)⟩

theorem massBitTree_encode {n : ℕ} (T : ℕ) (D : BinaryFractionalGuesses.Input n) :
    massBitTree T (SourcePacking.encode D.costs D.adjacency D.demands) =
      some ⟨n, EncodedVertexSolver.massBitTree T (BinaryFractionalGuesses.decodeInput D)⟩ := by
  simp [massBitTree, parse_encode]

theorem sizeBitTree_encode {n : ℕ} (T : ℕ) (D : BinaryFractionalGuesses.Input n) :
    sizeBitTree T (SourcePacking.encode D.costs D.adjacency D.demands) =
      some ⟨n, EncodedVertexSolver.sizeBitTree T (BinaryFractionalGuesses.decodeInput D)⟩ := by
  simp [sizeBitTree, parse_encode]

end DirectedFlowCutGap.EncodedVertexInput
