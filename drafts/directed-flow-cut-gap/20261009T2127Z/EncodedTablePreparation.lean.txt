import DirectedFlowCutGap.EncodedCellAccess

/-!
# Fixed preparation of retained finite tables

The input is retained finite row data, not an encoder or callback. Each actual
payload is copied by the closed `CopyExec` body, and every input list cell and
output pair constructor is charged. This supports flags, padded binary words,
and pairs of words used by the rational layer with the same representation.

`prepareRows` is called once by a producer; subsequent cell/tabulation calls
receive its retained result. The map expressions in refinements describe the
input representation only. No runtime map or Nat.bits conversion is supplied
for free. The producer of derived rows, such as tape materialization or a
candidate family, must still have its own fixed-body certificate.

As in SequenceAccess, list cases borrow retained subvalues. The final proved
representation overhead must account for this reference movement. This file
does not claim a closed whole-entry runtime theorem.
-/
namespace DirectedFlowCutGap.EncodedTablePreparation
open BinaryArithmetic EncodedSequenceAccess

/-- Copy each payload once while constructing the retained row spine. -/
def prepareRow : List Value → Value × ℕ
  | [] => (.empty,4)
  | x::xs =>
      let c := copy x
      let r := prepareRow xs
      (.pair c.1 r.1,c.2+r.2+8)

inductive RowExec : List Value → Value → ℕ → Prop
  | nil : RowExec [] .empty 4
  | cons (x : Value) (xs : List Value) (y out : Value) (q r : ℕ) :
      CopyExec x y q → RowExec xs out r → RowExec (x::xs) (.pair y out) (q+r+8)

theorem prepareRow_exec (xs : List Value) :
    RowExec xs (prepareRow xs).1 (prepareRow xs).2 := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons x xs _ _ _ _ (copy_exec x) ih

theorem RowExec.result {xs : List Value} {out : Value} {q : ℕ}
    (h : RowExec xs out q) : out = (prepareRow xs).1 ∧ q = (prepareRow xs).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs y out q r hc hr ih =>
      have hcopy := hc.result
      constructor <;> simp only [prepareRow,hcopy.1,hcopy.2,ih.1,ih.2]

theorem prepareRow_value (xs : List Value) : (prepareRow xs).1 = sequence xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [prepareRow,EncodedSequenceAccess.sequence,(copy_spec x).1,ih]

def rowBound (n S : ℕ) : ℕ := n*(4*S+8)+4

theorem prepareRow_bound (xs : List Value) (S : ℕ)
    (hs : ∀ x∈xs, x.size ≤ S) : (prepareRow xs).2 ≤ rowBound xs.length S := by
  induction xs with
  | nil => simp [prepareRow,rowBound]
  | cons x xs ih =>
      have hx := hs x (by simp)
      have ht := ih (fun y hy => hs y (by simp [hy]))
      have hc := (copy_spec x).2
      simp only [prepareRow,List.length_cons]
      unfold rowBound at *
      nlinarith

/-- The row body is fixed, so this constructor admits no callback parameter. -/
def prepareRows : List (List Value) → Value × ℕ
  | [] => (.empty,4)
  | row::rows =>
      let c := prepareRow row
      let r := prepareRows rows
      (.pair c.1 r.1,c.2+r.2+8)

inductive RowsExec : List (List Value) → Value → ℕ → Prop
  | nil : RowsExec [] .empty 4
  | cons (row : List Value) (rows : List (List Value)) (x out : Value) (q r : ℕ) :
      RowExec row x q → RowsExec rows out r →
      RowsExec (row::rows) (.pair x out) (q+r+8)

theorem prepareRows_exec (rows : List (List Value)) :
    RowsExec rows (prepareRows rows).1 (prepareRows rows).2 := by
  induction rows with
  | nil => exact .nil
  | cons row rows ih => exact .cons row rows _ _ _ _ (prepareRow_exec row) ih

theorem RowsExec.result {rows : List (List Value)} {out : Value} {q : ℕ}
    (h : RowsExec rows out q) : out = (prepareRows rows).1 ∧ q = (prepareRows rows).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons row rows x out q r hc hr ih =>
      have hrow := hc.result
      constructor <;> simp only [prepareRows,hrow.1,hrow.2,ih.1,ih.2]

theorem prepareRows_value (rows : List (List Value)) :
    (prepareRows rows).1 = sequence (rows.map sequence) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [prepareRows,List.map_cons,EncodedSequenceAccess.sequence,prepareRow_value,ih]

def rowsBound (n m S : ℕ) : ℕ := n*(rowBound m S+8)+4

theorem prepareRows_bound (rows : List (List Value)) (m S : ℕ)
    (hm : ∀ row∈rows, row.length ≤ m)
    (hs : ∀ row∈rows, ∀ x∈row, x.size ≤ S) :
    (prepareRows rows).2 ≤ rowsBound rows.length m S := by
  induction rows with
  | nil => simp [prepareRows,rowsBound]
  | cons row rows ih =>
      have hlen := hm row (by simp)
      have hc := prepareRow_bound row S (hs row (by simp))
      have hc' : (prepareRow row).2 ≤ rowBound m S := hc.trans (by
        unfold rowBound
        exact Nat.add_le_add_right (Nat.mul_le_mul_right (4*S+8) hlen) 4)
      have ht := ih (fun r hr => hm r (by simp [hr]))
        (fun r hr => hs r (by simp [hr]))
      simp only [prepareRows,List.length_cons]
      unfold rowsBound at *
      nlinarith

/-- Actual stored output size includes every copied payload and row spine. -/
theorem prepareRows_size (rows : List (List Value)) (m S : ℕ)
    (hm : ∀ row∈rows, row.length ≤ m)
    (hs : ∀ row∈rows, ∀ x∈row, x.size ≤ S) :
    (prepareRows rows).1.size ≤ rows.length*(m*(S+1)+2)+1 := by
  rw [prepareRows_value]
  have hrow : ∀ x∈rows.map sequence, x.size ≤ m*(S+1)+1 := by
    intro x hx
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hx
    exact (sequence_size_bound (hs row hr)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right (S+1) (hm row hr)) 1)
  simpa only [List.length_map,Nat.add_assoc] using sequence_size_bound hrow

/-- Concrete composition: retain the constructed table, then perform one read. -/
def prepareAndRead (rows : List (List Value)) (i j : Bits) : Option Value × ℕ :=
  let p := prepareRows rows
  let q := read2 i j p.1
  (q.1,p.2+q.2+8)

inductive PrepareReadExec (rows : List (List Value)) (i j : Bits) :
    Option Value → ℕ → Prop
  | run (table : Value) (out : Option Value) (p q : ℕ) :
      RowsExec rows table p → Read2Exec i j table out q →
      PrepareReadExec rows i j out (p+q+8)

theorem prepareAndRead_exec (rows : List (List Value)) (i j : Bits) :
    PrepareReadExec rows i j (prepareAndRead rows i j).1 (prepareAndRead rows i j).2 :=
  .run _ _ _ _ (prepareRows_exec rows) (read2_exec i j (prepareRows rows).1)

theorem prepareAndRead_value (rows : List (List Value)) (i j : Bits) :
    (prepareAndRead rows i j).1 = (rows[value i]?).bind (fun row => row[value j]?) := by
  simp only [prepareAndRead,prepareRows_value,read2_get]

theorem prepareAndRead_bound (rows : List (List Value)) (i j : Bits) (m B S : ℕ)
    (hi : i.length ≤ B) (hj : j.length ≤ B)
    (hm : ∀ row∈rows, row.length ≤ m)
    (hs : ∀ row∈rows, ∀ x∈row, x.size ≤ S) :
    (prepareAndRead rows i j).2 ≤ rowsBound rows.length m S+
      read2Bound rows.length m B S+8 := by
  have hp := prepareRows_bound rows m S hm hs
  have hr := read2_bound i j rows m B S hi hj hm hs
  simpa only [prepareAndRead,prepareRows_value] using Nat.add_le_add_right (Nat.add_le_add hp hr) 8

/-- The actual prepared value can be retained and consumed by the existing
word-cell callback. The map occurs only in the representation premise. -/
theorem prepared_word_cell {n m : ℕ} (table : Vector (Vector Bits m) n)
    (raw : List (List Value))
    (hraw : raw = table.toList.map (fun row => row.toList.map Value.word))
    (i : Fin n) (j : Fin m) (ib jb : Bits)
    (hi : value ib = i.val) (hj : value jb = j.val) :
    (EncodedCellAccess.word ib jb (prepareRows raw).1).1 = some table[i.val][j.val] := by
  rw [prepareRows_value,hraw]
  simpa only [EncodedCellAccess.wordTable,List.map_map,Function.comp_def] using
    EncodedCellAccess.word_get table i j ib jb hi hj

theorem prepared_flag_cell {n m : ℕ} (table : Vector (Vector Bool m) n)
    (raw : List (List Value))
    (hraw : raw = table.toList.map (fun row => row.toList.map Value.flag))
    (i : Fin n) (j : Fin m) (ib jb : Bits)
    (hi : value ib = i.val) (hj : value jb = j.val) :
    (EncodedCellAccess.flag ib jb (prepareRows raw).1).1 = some table[i.val][j.val] := by
  rw [prepareRows_value,hraw]
  simpa only [EncodedCellAccess.flagTable,List.map_map,Function.comp_def] using
    EncodedCellAccess.flag_get table i j ib jb hi hj

end DirectedFlowCutGap.EncodedTablePreparation
