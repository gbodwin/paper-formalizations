import OnlineReachabilityPreservers.SteinerThinBitLoadWork

/-! Initialize the thin load cells from binary dimensions. -/

namespace OnlineReachabilityPreservers

private def duplicateCellsWithWork {A : Type*} : List A → List A × ℕ
  | [] => ([],2)
  | x::rest =>
    let out := duplicateCellsWithWork rest
    (x::x::out.1,out.2+6)

private theorem duplicateCellsWithWork_replicate {A : Type*} (value : A) (count : ℕ) :
    duplicateCellsWithWork (List.replicate count value) = (List.replicate (2*count) value,6*count+2) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ,duplicateCellsWithWork,ih,Nat.mul_succ]

/-- Build a repeated list by doubling after each bit in the count. -/
def binaryReplicateWithWork {A : Type*} (value : A) : List Bool → List A × ℕ
  | [] => ([],2)
  | bit::rest =>
    let tail := binaryReplicateWithWork value rest
    let doubled := duplicateCellsWithWork tail.1
    (if bit then value::doubled.1 else doubled.1,tail.2+doubled.2+8)

/-- The count may contain high zero bits. Work is linear in the actual
output length and the length of the supplied bit list. -/
theorem binaryReplicateWithWork_spec {A : Type*} (value : A) (count : List Bool) :
    let out := binaryReplicateWithWork value count
    out.1 = List.replicate (binaryWordValue count) value ∧
      out.2 ≤ 6*binaryWordValue count+12*count.length+2 := by
  induction count with
  | nil => simp [binaryReplicateWithWork,binaryWordValue]
  | cons bit rest ih =>
    let tail := binaryReplicateWithWork value rest
    let doubled := duplicateCellsWithWork tail.1
    obtain ⟨tailValue,cost⟩ := ih
    change tail.1 = _ at tailValue
    change tail.2 ≤ _ at cost
    have doubledExact : doubled = (List.replicate (2*binaryWordValue rest) value,6*binaryWordValue rest+2) := by
      change duplicateCellsWithWork tail.1 = _
      rw [tailValue,duplicateCellsWithWork_replicate]
    constructor
    · change (if bit then value::doubled.1 else doubled.1) = _
      rw [doubledExact]
      cases bit
      · change List.replicate (2*binaryWordValue rest) value = List.replicate (0+2*binaryWordValue rest) value
        rw [Nat.zero_add]
      · change value::List.replicate (2*binaryWordValue rest) value = List.replicate (1+2*binaryWordValue rest) value
        rw [Nat.add_comm 1,List.replicate_succ]
    · change tail.2+doubled.2+8 ≤ 6*binaryWordValue (bit::rest)+12*(rest.length+1)+2
      rw [doubledExact]
      cases bit
      · change tail.2+(6*binaryWordValue rest+2)+8 ≤ 6*(0+2*binaryWordValue rest)+12*(rest.length+1)+2
        omega
      · change tail.2+(6*binaryWordValue rest+2)+8 ≤ 6*(1+2*binaryWordValue rest)+12*(rest.length+1)+2
        omega

/-- Construct the zero word, square the binary vertex count, and fill the
row-major table with that word. -/
def emptyBinaryThinLoadsWithWork (base width : List Bool) : List (List Bool) × ℕ :=
  let zero := binaryReplicateWithWork false width
  let size := mulBinaryWordsWithWork base base
  let cells := binaryReplicateWithWork zero.1 size.1
  (cells.1,zero.2+size.2+cells.2+6)

/-- Work for constructing the initial binary table, including every cell
and the shared zero word. -/
def emptyBinaryThinLoadWorkBudget (n width baseBits widthBits : ℕ) : ℕ :=
  6*width+12*widthBits+2+binaryMultiplicationWorkBudget baseBits baseBits+
    (6*(n*n)+12*(baseBits*(baseBits+2))+2)+6

private theorem binaryWordValue_replicate_false (width : ℕ) :
    binaryWordValue (List.replicate width false) = 0 := by
  induction width with
  | zero => rfl
  | succ width ih =>
    change 0+2*binaryWordValue (List.replicate width false) = 0
    rw [ih]

/-- The constructed fixed-width words encode exactly the existing initial
table. Empty and zero-padded dimensions are supported. -/
theorem emptyBinaryThinLoadsWithWork_spec {n : ℕ} (base width : List Bool) (size : binaryWordValue base = n) :
    let out := emptyBinaryThinLoadsWithWork base width
    EncodesThinLoadTable (emptyFinThinLoads n) out.1 (binaryWordValue width) ∧
      out.2 ≤ emptyBinaryThinLoadWorkBudget n (binaryWordValue width) base.length width.length := by
  let zero := binaryReplicateWithWork false width
  let square := mulBinaryWordsWithWork base base
  let cells := binaryReplicateWithWork zero.1 square.1
  obtain ⟨zeroWord,zeroCost⟩ := binaryReplicateWithWork_spec false width
  obtain ⟨dimension,narrow,multiply⟩ := mulBinaryWordsWithWork_spec base base
  obtain ⟨cellValues,cellCost⟩ := binaryReplicateWithWork_spec zero.1 square.1
  change binaryWordValue square.1 = _ at dimension
  rw [size] at dimension
  change zero.1 = _ at zeroWord
  change cells.1 = _ at cellValues
  rw [dimension,zeroWord] at cellValues
  refine ⟨?_,?_⟩
  · change EncodesThinLoadTable (emptyFinThinLoads n) cells.1 (binaryWordValue width)
    rw [cellValues]
    constructor
    · simp [emptyFinThinLoads,binaryWordValue_replicate_false]
    · intro word inside
      have same : word = List.replicate (binaryWordValue width) false := List.eq_of_mem_replicate inside
      simp [same]
  · change cells.2 ≤ _ at cellCost
    rw [dimension] at cellCost
    have cellBound : cells.2 ≤ 6*(n*n)+12*(base.length*(base.length+2))+2 := by
      change square.1.length ≤ _ at narrow
      omega
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add zeroCost multiply) cellBound) 6

end OnlineReachabilityPreservers
