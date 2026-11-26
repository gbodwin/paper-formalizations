import OnlineReachabilityPreservers.SteinerBinaryWeightedUpdateWork
import OnlineReachabilityPreservers.SteinerBinaryThinSampleWork

/-! Initialize the binary weighted table and derive its cover controls. -/

namespace OnlineReachabilityPreservers

open Finset

structure BinaryWeightedInitialTable (V : Type*) where
  rows : List (BinaryWeightedPairRow V)
  paid : List (V × V)
  paidLabels : List (List Bool × List Bool)
  total : ℕ
  work : ℕ

/-- Read the paid cost and labels at each pair. Build its zero-charge
state and pay for each cost encoding and each addition to the total. -/
def binaryWeightedInitialTableWithWork {V : Type*} (readCost : V × V → Option ℕ × ℕ)
    (readLabel : V → List Bool × ℕ) (width : ℕ) : List (V × V) → BinaryWeightedInitialTable V
  | [] => ⟨[],[],[],0,2⟩
  | e :: keys =>
    let cost := readCost e
    let left := readLabel e.1
    let right := readLabel e.2
    let labels := (left.1,right.1)
    let tail := binaryWeightedInitialTableWithWork readCost readLabel width keys
    let work := cost.2+left.2+right.2+tail.work
    match cost.1 with
    | none => ⟨⟨e,labels,none⟩ :: tail.rows,tail.paid,tail.paidLabels,tail.total,work+8⟩
    | some value =>
      let word := encodeBoundedNatWithBinaryWork value width
      let initial := binaryWeightedLoadZeroWithWork word.1
      ⟨⟨e,labels,some (word.1,initial.1)⟩ :: tail.rows,e :: tail.paid,labels :: tail.paidLabels,
        value+tail.total,work+word.2+initial.2+12⟩

def binaryWeightedInitialTableWorkBudget (keys width costRead labelRead : ℕ) : ℕ :=
  2+keys*(costRead+2*labelRead+boundedNatToBinaryWorkBudget width+16)

variable {V : Type*} [LinearOrder V]

/-- The table keeps the key order, represents zero charges with the
given cost width, and counts each paid key exactly once. -/
theorem binaryWeightedInitialTableWithWork_spec (keys : List (V × V)) (simple : keys.Nodup)
    (edges : Arcs V) (weight : V × V → ℕ) (readCost : V × V → Option ℕ × ℕ)
    (readLabel : V → List Bool × ℕ) (width costRead labelRead : ℕ)
    (costExact : ∀ e ∈ keys, (readCost e).1 = if e ∈ edges then some (weight e) else none)
    (costWork : ∀ e ∈ keys, (readCost e).2 ≤ costRead)
    (labelWork : ∀ v, (readLabel v).2 ≤ labelRead)
    (fits : ∀ e ∈ edges, weight e < 2^width) :
    let out := binaryWeightedInitialTableWithWork readCost readLabel width keys
    let code := fun v => (readLabel v).1
    out.rows.map BinaryWeightedPairRow.arc = keys ∧
    out.paid = keys.filter (fun e => decide (e ∈ edges)) ∧
    out.paidLabels = binaryEncodeArcs code out.paid ∧
    out.total = ∑ e ∈ keys.toFinset.filter (· ∈ edges), weight e ∧
    (∀ row ∈ out.rows, row.Encodes edges weight (fun _ => 0) code width width ∧ row.ChargeWidths 0 1) ∧
    out.work ≤ binaryWeightedInitialTableWorkBudget keys.length width costRead labelRead := by
  let code := fun v => (readLabel v).1
  let fee := costRead+2*labelRead+boundedNatToBinaryWorkBudget width+16
  induction keys with
  | nil => simp [binaryWeightedInitialTableWithWork,binaryWeightedInitialTableWorkBudget,binaryEncodeArcs]
  | cons e keys ih =>
    obtain ⟨fresh,remaining⟩ := List.nodup_cons.mp simple
    obtain ⟨keysEq,paidEq,labelsEq,totalEq,states,tailWork⟩ := ih remaining
      (fun k hk => costExact k (List.mem_cons_of_mem e hk)) (fun k hk => costWork k (List.mem_cons_of_mem e hk))
    let tail := binaryWeightedInitialTableWithWork readCost readLabel width keys
    let left := readLabel e.1
    let right := readLabel e.2
    have cost := costExact e List.mem_cons_self
    have costFee := costWork e List.mem_cons_self
    have leftFee : left.2 ≤ labelRead := labelWork e.1
    have rightFee : right.2 ≤ labelRead := labelWork e.2
    have tailBound : tail.work ≤ 2+keys.length*fee := tailWork
    have freshIn : e ∉ keys.toFinset.filter (· ∈ edges) := fun inFilter =>
      fresh (List.mem_toFinset.mp (Finset.mem_filter.mp inFilter).1)
    change tail.rows.map BinaryWeightedPairRow.arc = _ at keysEq
    change tail.paid = _ at paidEq
    change tail.paidLabels = binaryEncodeArcs code tail.paid at labelsEq
    change tail.total = _ at totalEq
    change ∀ row ∈ tail.rows, row.Encodes edges weight (fun _ => 0) code width width ∧ row.ChargeWidths 0 1 at states
    dsimp only [binaryWeightedInitialTableWithWork]
    rw [cost]
    by_cases present : e ∈ edges
    · simp only [present, ite_true]
      let word := encodeBoundedNatWithBinaryWork (weight e) width
      let seed := binaryWeightedLoadZeroWithWork word.1
      let row : BinaryWeightedPairRow V := ⟨e,(code e.1,code e.2),some (word.1,seed.1)⟩
      obtain ⟨value,count,wordFee⟩ := encodeBoundedNatWithBinaryWork_spec (weight e) width (fits e present)
      obtain ⟨zeroState,zeroFee⟩ := binaryWeightedLoadZeroWithWork_spec word.1
      change binaryWordValue word.1 = _ at value
      change word.1.length = _ at count
      change word.2 ≤ _ at wordFee
      change seed.2 = 4 at zeroFee
      refine ⟨congrArg (e :: ·) keysEq,?_,?_,?_,?_,?_⟩
      · simpa [present] using congrArg (e :: ·) paidEq
      · change row.labels :: tail.paidLabels = binaryEncodeArcs code (e :: tail.paid)
        rw [labelsEq]
        rfl
      · change weight e+tail.total = _
        simp only [List.toFinset_cons,Finset.filter_insert,present,ite_true,Finset.sum_insert freshIn,totalEq]
      · intro next member
        change next ∈ row :: tail.rows at member
        rcases List.mem_cons.mp member with rfl | member
        · refine ⟨⟨rfl,fun _ => ⟨word.1,seed.1,rfl,value,by simpa only [value] using zeroState,count.le,count.le⟩,
            fun absent => (absent present).elim⟩,?_⟩
          intro _ _ equal
          dsimp only [row] at equal
          cases equal
          exact ⟨le_rfl,le_rfl⟩
        · exact states next member
      · change (readCost e).2+left.2+right.2+tail.work+word.2+seed.2+12 ≤ 2+(keys.length+1)*fee
        rw [Nat.add_mul,Nat.one_mul]
        dsimp only [fee] at ⊢ tailBound
        omega
    · simp only [present, ite_false]
      let row : BinaryWeightedPairRow V := ⟨e,(code e.1,code e.2),none⟩
      refine ⟨congrArg (e :: ·) keysEq,?_,labelsEq,?_,?_,?_⟩
      · simpa [present] using paidEq
      · change tail.total = _
        simp only [totalEq,List.toFinset_cons,Finset.filter_insert,present,ite_false]
      · intro next member
        change next ∈ row :: tail.rows at member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨⟨rfl,fun impossible => (present impossible).elim,fun _ => rfl⟩,by simp [row,BinaryWeightedPairRow.ChargeWidths]⟩
        · exact states next member
      · change (readCost e).2+left.2+right.2+tail.work+8 ≤ 2+(keys.length+1)*fee
        rw [Nat.add_mul,Nat.one_mul]
        dsimp only [fee] at ⊢ tailBound
        omega

/-- With all pair keys present, the table gives the distinct paid arcs
and their exact unnormalized total cost. -/
theorem binaryWeightedInitialTableWithWork_complete (keys : List (V × V)) (simple : keys.Nodup)
    (complete : ∀ e, e ∈ keys) (edges : Arcs V) (weight : V × V → ℕ)
    (readCost : V × V → Option ℕ × ℕ) (readLabel : V → List Bool × ℕ) (width costRead labelRead : ℕ)
    (costExact : ∀ e ∈ keys, (readCost e).1 = if e ∈ edges then some (weight e) else none)
    (costWork : ∀ e ∈ keys, (readCost e).2 ≤ costRead) (labelWork : ∀ v, (readLabel v).2 ≤ labelRead)
    (fits : ∀ e ∈ edges, weight e < 2^width) :
    let out := binaryWeightedInitialTableWithWork readCost readLabel width keys
    out.paid.Nodup ∧ out.paid.toFinset = edges ∧ out.total = ∑ e ∈ edges, weight e := by
  obtain ⟨_,paid,_,total,_,_⟩ := binaryWeightedInitialTableWithWork_spec keys simple edges weight
    readCost readLabel width costRead labelRead costExact costWork labelWork fits
  let out := binaryWeightedInitialTableWithWork readCost readLabel width keys
  have full : keys.toFinset.filter (· ∈ edges) = edges := by
    ext e
    simp [complete e]
  change out.paid = _ at paid
  change out.total = _ at total
  change out.paid.Nodup ∧ out.paid.toFinset = edges ∧ out.total = _
  refine ⟨paid.symm ▸ simple.filter _,?_,total.trans (congrArg (fun es : Arcs V => ∑ e ∈ es, weight e) full)⟩
  rw [paid]
  ext e
  simp [complete e]

structure BinaryWeightedCoverControls where
  supply : ℕ
  fuel : ℕ
  ceiling : List Bool
  work : ℕ

/-- Derive the numeric scale and fuel from the accumulated paid cost,
and encode the scale at its measured width. -/
def binaryWeightedCoverControlsWithWork (total : ℕ) : BinaryWeightedCoverControls :=
  let scale := max 1 total
  let width := bitLengthWithWork scale
  let ceiling := encodeBoundedNatWithBinaryWork scale width.1
  ⟨scale,max 1 width.1*total+1,ceiling.1,width.2+ceiling.2+9⟩

theorem binaryWeightedCoverControlsWithWork_spec (total : ℕ) :
    let out := binaryWeightedCoverControlsWithWork total
    let scale := max 1 total
    out.supply = scale ∧ out.fuel = (scale.log2+1)*total+1 ∧ binaryWordValue out.ceiling = scale ∧
    out.ceiling.length = scale.size ∧ out.work ≤ 7*scale+3+boundedNatToBinaryWorkBudget scale.size+9 := by
  let scale := max 1 total
  let width := bitLengthWithWork scale
  have widthEq : width.1 = scale.size := (bitLengthWithWork_spec scale).1
  have fits : scale < 2^width.1 := by rw [widthEq]; exact Nat.size_le.mp le_rfl
  have fuel : max 1 width.1*total+1 = (scale.log2+1)*total+1 := by
    rw [widthEq,max_size_eq_log2_add_one]
  obtain ⟨value,length,encodeCost⟩ := encodeBoundedNatWithBinaryWork_spec scale width.1 fits
  have widthCost : width.2 ≤ 7*scale+3 := bitLengthWork_le scale
  rw [widthEq] at encodeCost
  have work : width.2+(encodeBoundedNatWithBinaryWork scale width.1).2+9 ≤
      7*scale+3+boundedNatToBinaryWorkBudget scale.size+9 := by
    rw [widthEq]
    exact Nat.add_le_add_right (Nat.add_le_add widthCost encodeCost) 9
  exact ⟨rfl,fuel,value,length.trans widthEq,work⟩

end OnlineReachabilityPreservers
