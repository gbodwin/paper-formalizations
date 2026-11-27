import OnlineReachabilityPreservers.SteinerBinaryInputDecoding

/-! Validate the advertised label width before decoding raw endpoint words. -/

namespace OnlineReachabilityPreservers

/-- Count the bits in the two words of each row. -/
def binaryEndpointBits (rows : List (List Bool × List Bool)) : ℕ :=
  (rows.map fun row => row.1.length + row.2.length).sum

/-- Scan word lengths and stop at the first row wider than the allowance. -/
def checkBinaryEndpointWidthsWithWork (width : ℕ) : List (List Bool × List Bool) → Bool × ℕ
  | [] => (true,2)
  | row::rest =>
    let left := row.1.length
    let right := row.2.length
    let charge := left+right+4*(width+1)+7
    if left ≤ width ∧ right ≤ width then
      let suffix := checkBinaryEndpointWidthsWithWork width rest
      (suffix.1,suffix.2+charge)
    else (false,charge)

/-- Work charged for scanning every raw word and checking every row. -/
def binaryEndpointWidthCheckBudget (width : ℕ) (rows : List (List Bool × List Bool)) : ℕ :=
  2 + binaryEndpointBits rows + rows.length*(4*(width+1)+7)

/-- The check recognizes precisely the permitted lengths, with the same
upper work allowance for successful and unsuccessful checks. -/
theorem checkBinaryEndpointWidthsWithWork_spec (width : ℕ) (rows : List (List Bool × List Bool)) :
    let checked := checkBinaryEndpointWidthsWithWork width rows
    (checked.1 = true ↔ ∀ row ∈ rows, row.1.length ≤ width ∧ row.2.length ≤ width) ∧
      checked.2 ≤ binaryEndpointWidthCheckBudget width rows := by
  induction rows with
  | nil => simp [checkBinaryEndpointWidthsWithWork,binaryEndpointWidthCheckBudget,binaryEndpointBits]
  | cons row rest ih =>
    obtain ⟨check,cost⟩ := ih
    change ((checkBinaryEndpointWidthsWithWork width (row::rest)).1 = true ↔ _) ∧ _
    rw [checkBinaryEndpointWidthsWithWork]
    dsimp only
    by_cases fits : row.1.length ≤ width ∧ row.2.length ≤ width
    · rw [ite_eq_left fits]
      simp only [check,List.forall_mem_cons,fits,true_and]
      simp only [binaryEndpointWidthCheckBudget,binaryEndpointBits,List.map_cons,List.sum_cons,
        List.length_cons,Nat.add_mul,Nat.one_mul] at cost ⊢
      omega
    · rw [ite_eq_right fits]
      simp only [Bool.false_eq_true,List.forall_mem_cons,fits,false_and,true_and]
      simp only [binaryEndpointWidthCheckBudget,binaryEndpointBits,List.map_cons,List.sum_cons,
        List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

/-- Check raw word lengths before passing them to the bounded decoder. -/
def decodeCheckedBinaryFinArcRowsWithWork {n : ℕ} (width : ℕ) (words : List (List Bool × List Bool)) :
    Option (List (Fin n × Fin n)) × ℕ :=
  let checked := checkBinaryEndpointWidthsWithWork width words
  if checked.1 then
    let decoded := decodeBinaryFinArcRowsWithWork (n := n) width words
    (decoded.1,checked.2+decoded.2+3)
  else (none,checked.2+3)

/-- The guarded decoder preserves the endpoint values and rejects words
wider than the allowance. -/
theorem decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff {n : ℕ} (width : ℕ)
    (words : List (List Bool × List Bool)) (rows : List (Fin n × Fin n)) :
    (decodeCheckedBinaryFinArcRowsWithWork (n := n) width words).1 = some rows ↔
      (∀ word ∈ words, word.1.length ≤ width ∧ word.2.length ≤ width) ∧
        rows.map (fun row => (row.1.val,row.2.val)) =
          words.map (fun word => (binaryWordValue word.1,binaryWordValue word.2)) := by
  obtain ⟨widths,_⟩ := checkBinaryEndpointWidthsWithWork_spec width words
  unfold decodeCheckedBinaryFinArcRowsWithWork
  dsimp only
  split
  · rename_i ok
    exact ⟨fun decoded => ⟨widths.mp ok,(decodeBinaryFinArcRowsWithWork_eq_some_iff width words rows).mp decoded⟩,
      fun accepted => (decodeBinaryFinArcRowsWithWork_eq_some_iff width words rows).mpr accepted.2⟩
  · rename_i failed
    constructor
    · intro impossible
      cases impossible
    · intro accepted
      exact (failed (widths.mpr accepted.1)).elim

/-- Accept exactly the rows whose two lengths and values fit. -/
theorem decodeCheckedBinaryFinArcRowsWithWork_some_iff_valid {n : ℕ} (width : ℕ)
    (words : List (List Bool × List Bool)) :
    (∃ rows, (decodeCheckedBinaryFinArcRowsWithWork (n := n) width words).1 = some rows) ↔
      ∀ word ∈ words, (word.1.length ≤ width ∧ word.2.length ≤ width) ∧
        (binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n) := by
  constructor
  · rintro ⟨rows,accepted⟩
    obtain ⟨fits,values⟩ := (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width words rows).mp accepted
    have decoded := (decodeBinaryFinArcRowsWithWork_eq_some_iff width words rows).mpr values
    have valid := (decodeBinaryFinArcRowsWithWork_some_iff_valid width words).mp ⟨rows,decoded⟩
    exact fun word on => ⟨fits word on,valid word on⟩
  · intro accepted
    have fits (word) (on : word ∈ words) := (accepted word on).1
    have valid (word) (on : word ∈ words) := (accepted word on).2
    obtain ⟨rows,decoded⟩ := (decodeBinaryFinArcRowsWithWork_some_iff_valid width words).mpr valid
    have values := (decodeBinaryFinArcRowsWithWork_eq_some_iff width words rows).mp decoded
    exact ⟨rows,(decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width words rows).mpr ⟨fits,values⟩⟩

/-- The guard's charge uses the actual raw bit count. Only rows that pass
need an allowance for arithmetic at the advertised width. -/
theorem decodeCheckedBinaryFinArcRowsWithWork_work_le {n : ℕ} (width : ℕ)
    (words : List (List Bool × List Bool)) :
    (decodeCheckedBinaryFinArcRowsWithWork (n := n) width words).2 ≤
      binaryEndpointWidthCheckBudget width words + binaryFinArcDecodingWorkBudget words.length width + 3 := by
  obtain ⟨widths,checkCost⟩ := checkBinaryEndpointWidthsWithWork_spec width words
  unfold decodeCheckedBinaryFinArcRowsWithWork
  dsimp only
  split
  · rename_i ok
    have decodeCost := decodeBinaryFinArcRowsWithWork_work_le_of_width (n := n) width words (widths.mp ok)
    omega
  · omega

end OnlineReachabilityPreservers
