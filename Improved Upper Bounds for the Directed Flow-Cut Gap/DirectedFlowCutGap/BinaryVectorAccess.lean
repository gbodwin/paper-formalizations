import DirectedFlowCutGap.CachedBinaryIndex

/-! Decode and check the binary index used by a retained vector read. -/
namespace DirectedFlowCutGap.BinaryVectorAccess

open BinaryArithmetic

private def index {n : ℕ} (i : Fin n) : Fin n × ℕ :=
  let bits := DirectNaturalView.encode i.val
  let checked := CachedBinaryIndex.compute n bits.1
  let decoded : Fin n := ⟨checked.address,by
    change (CachedBinaryIndex.compute n bits.1).address<n
    rw [(CachedBinaryIndex.values n bits.1).1]
    change value (DirectNaturalView.encode i.val).1<n
    rw [DirectNaturalView.encode_eq,BinaryNaturalView.encode_value]
    exact i.isLt⟩
  (decoded,bits.2+checked.work+2*bits.1.length+8)

private theorem index_value {n : ℕ} (i : Fin n) : (index i).1=i := by
  apply Fin.ext
  change (CachedBinaryIndex.compute n (DirectNaturalView.encode i.val).1).address=i.val
  rw [(CachedBinaryIndex.values ..).1,DirectNaturalView.encode_eq,BinaryNaturalView.encode_value]

def read {A : Type} {n : ℕ} (v : Vector A n) (i : Fin n) : A × ℕ :=
  let position := index i
  (v[position.1.val],position.2)

@[simp] theorem read_value {A : Type} {n : ℕ} (v : Vector A n) (i : Fin n) : (read v i).1=v[i.val] := by
  change v[(index i).1.val]=v[i.val]
  simp only [index_value]

def budget {R : Type*} [Semiring R] (width : R) : R := 16*(width+1)^2+128*(width+2)^2+2*width+8

theorem read_paid {A : Type} {n width : ℕ} (v : Vector A n) (i : Fin n) (fits : n.size≤width) :
    (read v i).2≤budget width := by
  let bits := DirectNaturalView.encode i.val
  have current : i.val.size≤width := (Nat.size_le_size i.isLt.le).trans fits
  have stored : bits.1.length≤width := by
    change (DirectNaturalView.encode i.val).1.length≤width
    rw [DirectNaturalView.encode_eq,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]
    exact current
  have encoded : bits.2≤16*(width+1)^2 := by
    change (DirectNaturalView.encode i.val).2≤16*(width+1)^2
    rw [DirectNaturalView.encode_eq]
    exact (BinaryNaturalView.encode_paid _).trans (by gcongr)
  have checked := CachedBinaryIndex.paid bits.1 stored fits
  change bits.2+(CachedBinaryIndex.compute n bits.1).work+2*bits.1.length+8≤budget width
  unfold budget
  omega

def readMatrix {A : Type} {m n : ℕ} (matrix : Vector (Vector A n) m) (i : Fin m) (j : Fin n) : A × ℕ :=
  let row := read matrix i
  let cell := read row.1 j
  (cell.1,row.2+cell.2)

@[simp] theorem readMatrix_value {A : Type} {m n : ℕ} (matrix : Vector (Vector A n) m) (i : Fin m) (j : Fin n) :
    (readMatrix matrix i j).1=matrix[i.val][j.val] := by
  simp only [readMatrix,read_value]

theorem readMatrix_paid {A : Type} {m n width : ℕ} (matrix : Vector (Vector A n) m) (i : Fin m) (j : Fin n)
    (outer : m.size≤width) (inner : n.size≤width) : (readMatrix matrix i j).2 ≤ 2*budget width := by
  have all := Nat.add_le_add (read_paid matrix i outer) (read_paid (read matrix i).1 j inner)
  simpa only [readMatrix,two_mul] using all

end DirectedFlowCutGap.BinaryVectorAccess
