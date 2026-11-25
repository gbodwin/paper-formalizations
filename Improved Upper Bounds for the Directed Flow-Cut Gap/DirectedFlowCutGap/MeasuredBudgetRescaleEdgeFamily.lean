import DirectedFlowCutGap.BinaryRationalBudget
import DirectedFlowCutGap.ChargedThresholdPreservation
import DirectedFlowCutGap.RationalBudgetedRescaleEdgeFamily

/-! Binary preparation for the original-budget edge sampler. The returned
weights may use unreduced fractions, with the same values as the reference
rescaling. Record the arithmetic and typed matrix work of preparation. -/
namespace DirectedFlowCutGap.MeasuredBudgetRescaleEdgeFamily

open scoped BigOperators NNRat NNReal
open BinaryFractionalWalkOracle (Adjacency adjacent graph)
open BinaryRational (Fraction StoredBounded decode zero one halfDimension budgetGain)
open RationalEdgeThresholds (Weights weights demands)
open RationalExactEdgeOracle (Edge)
open RationalEdgeDecomposition (originalWeight originalWeight_eq originalTotal)
open RationalTrimmedEdgeFamily (trimmed cutoff)
open RationalPrunedEdgeFamily (indices)

variable {n : ℕ}

private def cell {T : Type*} (table : Vector (Vector T n) n) (e : Edge n) : T :=
  table[e.1.val][e.2.val]

private def tabulate {T : Type*} (f : Edge n → T) : Vector (Vector T n) n :=
  Vector.ofFn fun u => Vector.ofFn fun v => f (u,v)

@[simp] private theorem cell_tabulate {T : Type*} (f : Edge n → T) (e : Edge n) :
    cell (tabulate f) e = f e := by
  rcases e with ⟨u,v⟩
  simp [cell,tabulate]

private def rational (a : Fraction) : ℚ≥0 := (decode a).value

private structure Entry where
  original : Fraction
  scalable : Fraction
  saturated : Bool

private def inspect (A : Adjacency n) (w : Weights n) (limit : Fraction) (e : Edge n) : Entry × ℕ :=
  let arc := adjacent A e.1 e.2
  if arc.1 then
    let a := cell w e
    let small := BinaryRational.le a limit
    if small.1 then (⟨a,zero,false⟩,arc.2+small.2+10) else
      let large := BinaryRational.le one a
      (⟨a,if large.1 then zero else a,large.1⟩,arc.2+small.2+large.2+14)
  else (⟨zero,zero,false⟩,arc.2+5)

private def Entry.reserve (r : Entry) : Fraction := if r.saturated then one else zero

private def emit (g : Fraction) (r : Entry) : Fraction × ℕ :=
  if r.saturated then (one,3) else
    let result := BinaryRational.mul g r.scalable
    (result.1,result.2+3)

private theorem trimmed_original (A : Adjacency n) (w : Weights n) (e : Edge n) :
    originalWeight A (trimmed A w) e =
      if originalWeight A w e ≤ cutoff n then 0 else originalWeight A w e := by
  apply (NNRat.cast_injective (α := ℝ≥0))
  rw [originalWeight_eq]
  by_cases arc : (graph A).Adj e.1 e.2
  · rw [actualEdgeWeight_of_adj _ _ arc,RationalTrimmedEdgeFamily.trimmed_value]
    unfold ExactFlowCutGap.trimmedForSlack
    rw [← originalWeight_eq,← RationalTrimmedEdgeFamily.cutoff_value]
    dsimp only
    rw [NNRat.cast_le]
    split <;> simp
  · rw [actualEdgeWeight_of_not_adj _ _ arc]
    have orig : originalWeight A w e = 0 := by
      apply (NNRat.cast_injective (α := ℝ≥0))
      rw [originalWeight_eq,actualEdgeWeight_of_not_adj _ _ arc,NNRat.cast_zero]
    simp [orig]

private theorem compare_value (a b : Fraction) :
    (BinaryRational.le a b).1 = true ↔ rational a ≤ rational b := by
  simp only [BinaryRational.le_decode,RawNonnegativeRational.Code.le_eq_true,rational]

private theorem inspect_values (A : Adjacency n) (w : Weights n) (e : Edge n) :
    let r := (inspect A w (halfDimension n).1 e).1
    let t := originalWeight A (trimmed A w) e
    rational r.original = originalWeight A w e ∧
      rational r.scalable = (if 1 ≤ t then 0 else t) ∧
      (r.saturated = true ↔ 1 ≤ t) := by
  dsimp only
  rw [trimmed_original]
  by_cases arc : A[e.1.val][e.2.val] = true
  · have actual : (adjacent A e.1 e.2).1 = true := arc
    have same : originalWeight A w e = rational (cell w e) := by
      rcases e with ⟨u,v⟩
      simp [originalWeight,arc,RationalEdgeDecomposition.weightQ,RationalEdgeThresholds.cost,
        BinaryFractionalWalkOracle.decodeCost,rational,cell]
    have limit : rational (halfDimension n).1 = cutoff n := BinaryRational.halfDimension_value n
    have trimTest : (BinaryRational.le (cell w e) (halfDimension n).1).1 = true ↔
        rational (cell w e) ≤ cutoff n := by rw [compare_value,limit]
    have satTest : (BinaryRational.le one (cell w e)).1 = true ↔ 1 ≤ rational (cell w e) := by
      simp only [compare_value,rational,BinaryRational.decode_one,RawNonnegativeRational.Code.value_one]
    unfold inspect
    dsimp only
    rw [ite_eq_left actual,same]
    by_cases small : rational (cell w e) ≤ cutoff n
    · rw [ite_eq_left (trimTest.mpr small),ite_eq_left small]
      norm_num [rational]
    · have rejected : ¬ (BinaryRational.le (cell w e) (halfDimension n).1).1 = true :=
        fun h => small (trimTest.mp h)
      rw [ite_eq_right rejected,ite_eq_right small]
      by_cases large : 1 ≤ rational (cell w e)
      · have tested := satTest.mpr large
        simp only [tested,ite_eq_left large,ite_true]
        simp [rational,show 1 ≤ (decode (cell w e)).value from large]
      · have lower : ¬ (BinaryRational.le one (cell w e)).1 = true := fun h => large (satTest.mp h)
        simp only [ite_eq_right large,lower]
        simpa using (lt_of_not_ge large)
  · have absent : ¬ (adjacent A e.1 e.2).1 = true := arc
    simp [inspect,absent,originalWeight,arc,rational]

private theorem emit_value (g : Fraction) (r : Entry) :
    rational (emit g r).1 = if r.saturated then 1 else rational g * rational r.scalable := by
  unfold emit
  split <;> simp [rational]

private theorem indices_nodup (n : ℕ) : (indices n).Nodup := by
  unfold indices
  rw [List.nodup_flatMap]
  refine ⟨fun s _ => (List.nodup_finRange n).map (fun _ _ h => congrArg Prod.snd h),?_⟩
  refine (List.nodup_finRange n).imp fun distinct => List.disjoint_left.mpr ?_
  intro e left right
  obtain ⟨v,_,atLeft⟩ := List.mem_map.mp left
  obtain ⟨u,_,atRight⟩ := List.mem_map.mp right
  exact distinct (congrArg Prod.fst (atLeft.trans atRight.symm))

private theorem rowMajor_sum {T : Type*} [AddCommMonoid T] (f : Edge n → T) :
    ((indices n).map f).sum = ∑ e, f e := by
  rw [← List.sum_toFinset _ (indices_nodup n)]
  congr 1
  ext e
  refine ⟨fun _ => Finset.mem_univ _,fun _ => List.mem_toFinset.mpr ?_⟩
  exact List.mem_flatMap.mpr ⟨e.1,List.mem_finRange _,List.mem_map.mpr ⟨e.2,List.mem_finRange _,rfl⟩⟩

private theorem sum_value (xs : List Fraction) :
    rational (BinaryFractionalRows.sum xs).1 = (xs.map rational).sum := by
  induction xs with
  | nil => simp [BinaryFractionalRows.sum,rational]
  | cons a tail ih =>
    simp only [BinaryFractionalRows.sum,List.map_cons,List.sum_cons,rational,BinaryRational.add_decode,
      RawNonnegativeRational.Code.value_add] at ih ⊢
    rw [ih]

private theorem sum_unit_denominator (xs : List Fraction)
    (oneDen : ∀ a ∈ xs, (decode a).den = 1) :
    (decode (BinaryFractionalRows.sum xs).1).den = 1 := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    have front := oneDen a List.mem_cons_self
    have rest := ih (fun b hb => oneDen b (List.mem_cons_of_mem _ hb))
    simp only [BinaryFractionalRows.sum,BinaryRational.add_decode,RawNonnegativeRational.Code.add,front,rest,Nat.mul_one]

private def table (A : Adjacency n) (w : Weights n) (limit : Fraction) : Vector (Vector (Entry × ℕ) n) n :=
  tabulate (inspect A w limit)

private def column (labels : List (Edge n)) (records : Vector (Vector (Entry × ℕ) n) n) (extract : Entry → Fraction) :
    List Fraction :=
  labels.map fun e => extract (cell records e).1

private def preparedGain (labels : List (Edge n)) (records : Vector (Vector (Entry × ℕ) n) n) : Fraction × ℕ :=
  let original := BinaryFractionalRows.sum (column labels records Entry.original)
  let fixed := BinaryFractionalRows.sum (column labels records Entry.reserve)
  let subunit := BinaryFractionalRows.sum (column labels records Entry.scalable)
  let g := budgetGain original.1 fixed.1.num subunit.1
  (g.1,original.2+fixed.2+subunit.2+g.2)

private theorem column_value (A : Adjacency n) (w : Weights n) (f : Entry → Fraction) :
    rational (BinaryFractionalRows.sum (column (indices n) (table A w (halfDimension n).1) f)).1 =
      ∑ e, rational (f (inspect A w (halfDimension n).1 e).1) := by
  rw [sum_value]
  unfold column
  simp only [List.map_map,table,cell_tabulate]
  exact rowMajor_sum _

private theorem prepareGain_value (A : Adjacency n) (w : Weights n) :
    rational (preparedGain (indices n) (table A w (halfDimension n).1)).1 = RationalBudgetedRescaleEdgeFamily.multiplier A w := by
  let records := table A w (halfDimension n).1
  have original : rational (BinaryFractionalRows.sum (column (indices n) records Entry.original)).1 = originalTotal A w := by
    rw [column_value]
    exact Finset.sum_congr rfl fun e _ => (inspect_values A w e).1
  have subunit : rational (BinaryFractionalRows.sum (column (indices n) records Entry.scalable)).1 =
      ∑ e, if 1 ≤ originalWeight A (trimmed A w) e then (0 : ℚ≥0) else originalWeight A (trimmed A w) e := by
    rw [column_value]
    exact Finset.sum_congr rfl fun e _ => (inspect_values A w e).2.1
  have fixed : rational (BinaryFractionalRows.sum (column (indices n) records Entry.reserve)).1 =
      ∑ e, if 1 ≤ originalWeight A (trimmed A w) e then (1 : ℚ≥0) else 0 := by
    rw [column_value]
    refine Finset.sum_congr rfl fun e _ => ?_
    have condition := (inspect_values A w e).2.2
    unfold Entry.reserve
    by_cases large : 1 ≤ originalWeight A (trimmed A w) e
    · rw [ite_eq_left (condition.mpr large),ite_eq_left large]
      simp [rational]
    · rw [ite_eq_right (fun h => large (condition.mp h)),ite_eq_right large]
      simp [rational]
  have denominator := sum_unit_denominator (column (indices n) records Entry.reserve) (by
    intro a ha
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
    unfold Entry.reserve
    split <;> rfl)
  have count : (BinaryArithmetic.value (BinaryFractionalRows.sum (column (indices n) records Entry.reserve)).1.num : ℚ≥0) =
      rational (BinaryFractionalRows.sum (column (indices n) records Entry.reserve)).1 := by
    unfold rational RawNonnegativeRational.Code.value
    rw [denominator]
    simp [decode]
  unfold preparedGain
  dsimp only
  unfold rational
  rw [BinaryRational.budgetGain_value,count]
  change (if rational _ = 0 then 1 else min 2 ((rational _ - rational _) / rational _)) = _
  rw [original,subunit,fixed,RationalBudgetedRescaleEdgeFamily.multiplier_from_sums]

/- The typed layout allowance covers the shared pair enumeration, table
traversals, record copies and final assembly in the retained-array model. -/
private def layoutBudget (n : ℕ) : ℕ := 256*n*n+128*n+64

/-- Rescaled fractions and the preparation charge before the demand check. -/
def rescale (A : Adjacency n) (w : Weights n) : Weights n × ℕ :=
  let labels := indices n
  let limit := halfDimension n
  let records := table A w limit.1
  let gain := preparedGain labels records
  let output := tabulate fun e => emit gain.1 (cell records e).1
  let inputWork := (labels.map fun e => (cell records e).2).sum
  let outputWork := (labels.map fun e => (cell output e).2).sum
  (tabulate (fun e => (cell output e).1),
    limit.2+inputWork+gain.2+outputWork+layoutBudget n)

private theorem rescale_cell_value (A : Adjacency n) (w : Weights n) (e : Edge n) :
    rational (cell (rescale A w).1 e) = rational (cell (RationalBudgetedRescaleEdgeFamily.rescaled A w) e) := by
  have reference : rational (cell (RationalBudgetedRescaleEdgeFamily.rescaled A w) e) =
      RationalBudgetedRescaleEdgeFamily.scaledWeight (RationalBudgetedRescaleEdgeFamily.multiplier A w)
        (originalWeight A (trimmed A w) e) := by
    rcases e with ⟨u,v⟩
    simp [RationalBudgetedRescaleEdgeFamily.rescaled,cell,rational,BinaryRawRational.encode_eq]
  rw [reference]
  simp only [rescale,cell_tabulate,emit_value]
  rw [prepareGain_value]
  simp only [table,cell_tabulate]
  have h := inspect_values A w e
  unfold RationalBudgetedRescaleEdgeFamily.scaledWeight
  by_cases large : 1 ≤ originalWeight A (trimmed A w) e
  · rw [ite_eq_left (h.2.2.mpr large),ite_eq_left large]
  · rw [ite_eq_right (fun yes => large (h.2.2.mp yes)),ite_eq_right large,h.2.1,ite_eq_right large]

theorem rescale_weights (A : Adjacency n) (w : Weights n) :
    weights (rescale A w).1 = weights (RationalBudgetedRescaleEdgeFamily.rescaled A w) := by
  funext e
  exact congrArg (fun q : ℚ≥0 => (q : ℝ≥0)) (rescale_cell_value A w e)

private theorem stored_mono {f : Fraction} {a b : ℕ} (fit : StoredBounded f a) (more : a ≤ b) :
    StoredBounded f b :=
  ⟨fit.1.trans more,fit.2.trans more⟩

private theorem zero_stored (B : ℕ) (h : 1 ≤ B) : StoredBounded zero B := by
  simp [StoredBounded,zero,h]

private theorem one_stored (B : ℕ) (h : 1 ≤ B) : StoredBounded one B := by
  simp [StoredBounded,one,h]

private def operandWidth (n B : ℕ) : ℕ := B+n.size+2

private def sumWidth (n B : ℕ) : ℕ := n*n*(operandWidth n B+1)+1

private def gainWidth (n B : ℕ) : ℕ := 2*sumWidth n B+2

def outputWidth (n B : ℕ) : ℕ := gainWidth n B+operandWidth n B+1

private def entryBudget (B : ℕ) : ℕ := 4096*(B+1)^2+32

private def emitBudget (G B : ℕ) : ℕ := 2048*(G+B+1)^2+3

private theorem inspect_fits (A : Adjacency n) (w : Weights n) (limit : Fraction) (e : Edge n)
    (B : ℕ) (positive : 1 ≤ B) (fit : StoredBounded (cell w e) B) :
    let out := (inspect A w limit e).1
    StoredBounded out.original B ∧ StoredBounded out.scalable B ∧ StoredBounded out.reserve B := by
  have z := zero_stored B positive
  have o := one_stored B positive
  unfold inspect
  dsimp only
  split
  · split
    · exact ⟨fit,z,z⟩
    · refine ⟨fit,?_,?_⟩
      · split
        · exact z
        · exact fit
      · unfold Entry.reserve
        dsimp only
        split
        · exact o
        · exact z
  · exact ⟨z,z,z⟩

private theorem inspect_paid (A : Adjacency n) (w : Weights n) (limit : Fraction) (e : Edge n)
    (B : ℕ) (positive : 1 ≤ B) (fitWeight : StoredBounded (cell w e) B) (fitLimit : StoredBounded limit B) :
    (inspect A w limit e).2 ≤ entryBudget B := by
  have read := BinaryFractionalWalkBounds.adjacent_charge A e.1 e.2
  have small := BinaryRational.le_charge fitWeight fitLimit
  have large := BinaryRational.le_charge (one_stored B positive) fitWeight
  unfold inspect entryBudget
  dsimp only
  split
  · split <;> dsimp only <;> omega
  · dsimp only
    omega

private theorem emit_fits (g : Fraction) (r : Entry) {G B : ℕ}
    (fitGain : StoredBounded g G) (fitWeight : StoredBounded r.scalable B) :
    StoredBounded (emit g r).1 (G+B+1) := by
  unfold emit
  dsimp only
  split
  · exact one_stored _ (by omega)
  · exact BinaryRational.mul_stored_bounded (BinaryFractionalRows.stored_raw_bound fitGain)
      (BinaryFractionalRows.stored_raw_bound fitWeight)

private theorem emit_paid (g : Fraction) (r : Entry) {G B : ℕ}
    (fitGain : StoredBounded g G) (fitWeight : StoredBounded r.scalable B) :
    (emit g r).2 ≤ emitBudget G B := by
  have product := BinaryRational.mul_charge
    (stored_mono fitGain (show G ≤ G+B from by omega))
    (stored_mono fitWeight (show B ≤ G+B from by omega))
  unfold emit emitBudget
  dsimp only
  split <;> dsimp only <;> omega

private theorem indices_length (n : ℕ) : (indices n).length = n*n := by
  simp [indices,List.length_flatMap]

private theorem sum_map_bound {T : Type*} (xs : List T) (fee : T → ℕ) (B : ℕ)
    (bounded : ∀ x ∈ xs, fee x ≤ B) : (xs.map fee).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
    have first := bounded a List.mem_cons_self
    have rest := ih (fun x mem => bounded x (List.mem_cons_of_mem _ mem))
    simp only [List.map_cons,List.length_cons,List.sum_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem table_entry_fits (A : Adjacency n) (w : Weights n) (B : ℕ)
    (fits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B) (e : Edge n) :
    let r := (cell (table A w (halfDimension n).1) e).1
    StoredBounded r.original (operandWidth n B) ∧ StoredBounded r.scalable (operandWidth n B) ∧
      StoredBounded r.reserve (operandWidth n B) := by
  simp only [table,cell_tabulate]
  exact inspect_fits A w _ e _ (by unfold operandWidth; omega)
    (stored_mono (fits e.1 e.2) (by unfold operandWidth; omega))

private theorem column_bounds (records : Vector (Vector (Entry × ℕ) n) n) (f : Entry → Fraction) (B : ℕ)
    (fits : ∀ e, StoredBounded (f (cell records e).1) B) :
    StoredBounded (BinaryFractionalRows.sum (column (indices n) records f)).1 (n*n*(B+1)+1) ∧
      (BinaryFractionalRows.sum (column (indices n) records f)).2 ≤ BinaryFractionalRows.sumBound (n*n) B := by
  have common : ∀ a ∈ column (indices n) records f, StoredBounded a B := by
    intro a ha
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
    exact fits e
  have length : (column (indices n) records f).length = n*n := by simp [column,indices_length]
  have width := BinaryFractionalRows.sum_stored_bound (column (indices n) records f) B
    (fun a ha => BinaryFractionalRows.stored_raw_bound (common a ha))
  have paid := BinaryFractionalRows.sum_charge (column (indices n) records f) B common
  rw [length] at width paid
  exact ⟨width,paid⟩

private theorem preparedGain_bounds (A : Adjacency n) (w : Weights n) (B : ℕ)
    (fits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B) :
    let result := preparedGain (indices n) (table A w (halfDimension n).1)
    StoredBounded result.1 (gainWidth n B) ∧ result.2 ≤
      3 * BinaryFractionalRows.sumBound (n*n) (operandWidth n B) + BinaryRational.budgetGainBound (sumWidth n B) := by
  let records := table A w (halfDimension n).1
  let width := operandWidth n B
  have original := column_bounds records Entry.original width (fun e => (table_entry_fits A w B fits e).1)
  have fixed := column_bounds records Entry.reserve width (fun e => (table_entry_fits A w B fits e).2.2)
  have subunit := column_bounds records Entry.scalable width (fun e => (table_entry_fits A w B fits e).2.1)
  refine ⟨BinaryRational.budgetGain_stored _ _ _ (sumWidth n B) original.1 subunit.1,?_⟩
  have gain := BinaryRational.budgetGain_paid _ _ _ (sumWidth n B) original.1 fixed.1.1 subunit.1
  change (preparedGain (indices n) records).2 ≤ 3 * BinaryFractionalRows.sumBound (n*n) width + _
  change (BinaryFractionalRows.sum (column (indices n) records Entry.original)).2 +
    (BinaryFractionalRows.sum (column (indices n) records Entry.reserve)).2 +
    (BinaryFractionalRows.sum (column (indices n) records Entry.scalable)).2 +
    (budgetGain (BinaryFractionalRows.sum (column (indices n) records Entry.original)).1
      (BinaryFractionalRows.sum (column (indices n) records Entry.reserve)).1.num
      (BinaryFractionalRows.sum (column (indices n) records Entry.scalable)).1).2 ≤ _
  omega

def rescaleBudget (n B : ℕ) : ℕ :=
  16*(n.size+1)^2+6 + n*n*entryBudget (operandWidth n B) +
    (3 * BinaryFractionalRows.sumBound (n*n) (operandWidth n B) + BinaryRational.budgetGainBound (sumWidth n B)) +
    n*n*emitBudget (gainWidth n B) (operandWidth n B) + layoutBudget n

theorem rescale_bounds (A : Adjacency n) (w : Weights n) (B : ℕ)
    (fits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B) :
    (∀ s t : Fin n, StoredBounded (rescale A w).1[s.val][t.val] (outputWidth n B)) ∧
      (rescale A w).2 ≤ rescaleBudget n B := by
  let records := table A w (halfDimension n).1
  let gain := preparedGain (indices n) records
  let output := tabulate fun e => emit gain.1 (cell records e).1
  have gainFit := preparedGain_bounds A w B fits
  have atEntry (e : Edge n) := (table_entry_fits A w B fits e).2.1
  constructor
  · intro s t
    change StoredBounded (cell (rescale A w).1 (s,t)) (outputWidth n B)
    change StoredBounded (cell (tabulate fun e => (cell output e).1) (s,t)) (outputWidth n B)
    simp only [cell_tabulate,output]
    exact emit_fits _ _ gainFit.1 (atEntry (s,t))
  · have limit := BinaryRational.halfDimension_paid n
    have width : StoredBounded (halfDimension n).1 (operandWidth n B) :=
      stored_mono (BinaryRational.halfDimension_stored n) (by unfold operandWidth; omega)
    have inputWork := sum_map_bound (indices n) (fun e => (cell records e).2) (entryBudget (operandWidth n B)) (by
      intro e _
      simp only [records,table,cell_tabulate]
      exact inspect_paid A w _ e _ (by unfold operandWidth; omega)
        (stored_mono (fits e.1 e.2) (by unfold operandWidth; omega)) width)
    have outputWork := sum_map_bound (indices n) (fun e => (cell output e).2)
      (emitBudget (gainWidth n B) (operandWidth n B)) (by
      intro e _
      simp only [output,cell_tabulate]
      exact emit_paid _ _ gainFit.1 (atEntry e))
    rw [indices_length] at inputWork outputWork
    have done : gain.2 ≤ 3 * BinaryFractionalRows.sumBound (n*n) (operandWidth n B) +
        BinaryRational.budgetGainBound (sumWidth n B) := gainFit.2
    change (halfDimension n).2 + ((indices n).map fun e => (cell records e).2).sum +
      gain.2 + ((indices n).map fun e => (cell output e).2).sum + layoutBudget n ≤ _
    unfold rescaleBudget
    omega

structure Preparation (n : ℕ) where
  proposed : Weights n
  preserves : Bool
  work : ℕ

/-- Perform the binary rescaling and test all original threshold demands. -/
def prepare (A : Adjacency n) (w : Weights n) : Preparation n :=
  let r := rescale A w
  let guard := ChargedThresholdPreservation.check A w r.1
  ⟨r.1,guard.1,r.2+guard.2+5⟩

def prepareBudget (n B : ℕ) : ℕ :=
  rescaleBudget n B + ChargedThresholdPreservation.budget n B (outputWidth n B) + 5

theorem prepare_paid (A : Adjacency n) (w : Weights n) (B : ℕ)
    (fits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B) :
    (prepare A w).work ≤ prepareBudget n B := by
  have h := rescale_bounds A w B fits
  have guard := ChargedThresholdPreservation.check_paid A w (rescale A w).1 fits h.1
  exact Nat.add_le_add_right (Nat.add_le_add h.2 guard) _

private theorem demands_congr (A : Adjacency n) {q r : Weights n}
    (same : weights q = weights r) : demands A q = demands A r := by
  have far : RationalEdgeThresholds.far A q = RationalEdgeThresholds.far A r := by
    funext e
    apply Bool.eq_iff_iff.mpr
    simp only [RationalEdgeThresholds.far_iff,same]
  unfold demands
  rw [far]

theorem prepare_preserves (A : Adjacency n) (w : Weights n) :
    (prepare A w).preserves = RationalBudgetedRescaleEdgeFamily.eligible A w := by
  have same := demands_congr A (rescale_weights A w)
  change (ChargedThresholdPreservation.check A w (rescale A w).1).1 = _
  rw [ChargedThresholdPreservation.check_value]
  unfold RationalBudgetedRescaleEdgeFamily.eligible RationalPrunedEdgeFamily.preserves
  rw [same]

private theorem factor_congr (A : Adjacency n) {q r : Weights n} (same : weights q = weights r) :
    RationalInstanceEdgeFactor.leastSupported A q = RationalInstanceEdgeFactor.leastSupported A r := by
  simp only [RationalInstanceEdgeFactor.leastSupported_eq]
  apply le_antisymm
  · apply RationalInstanceEdgeFactor.least_le_of_factor A q
    rw [same]
    exact RationalInstanceEdgeFactor.least_valid A r
  · apply RationalInstanceEdgeFactor.least_le_of_factor A r
    rw [← same]
    exact RationalInstanceEdgeFactor.least_valid A q

private theorem adaptive_congr (A : Adjacency n) {q r : Weights n} (same : weights q = weights r) (a : ℚ≥0) :
    RationalOriginalEdgeFamily.adaptive A q a = RationalOriginalEdgeFamily.adaptive A r a := by
  have arc (e : Edge n) : originalWeight A q e = originalWeight A r e := by
    apply (NNRat.cast_injective (α := ℝ≥0))
    simp only [originalWeight_eq,same]
  have light (k : ℕ) : RationalOriginalEdgeFamily.light A q a k = RationalOriginalEdgeFamily.light A r a k := by
    simp only [RationalOriginalEdgeFamily.light,arc]
  have total : originalTotal A q = originalTotal A r := by simp only [originalTotal,arc]
  have scale : RationalOriginalEdgeFamily.chooseScale A q a = RationalOriginalEdgeFamily.chooseScale A r a := by
    have mass : RationalOriginalEdgeFamily.lightMass A q a n = RationalOriginalEdgeFamily.lightMass A r a n := by
      simp only [RationalOriginalEdgeFamily.lightMass,light,arc]
    exact congrArg (fun m : ℚ≥0 => if m ≤ 1/4 then n else max 1 (RationalExactEdgeOracle.arcSet A).card) mass
  have budget (k : ℕ) : RationalOriginalEdgeFamily.horizon A q a k = RationalOriginalEdgeFamily.horizon A r a k := by
    simp only [RationalOriginalEdgeFamily.horizon,total]
  by_cases empty : a = 0
  · simp [RationalOriginalEdgeFamily.adaptive,empty]
  · simp only [RationalOriginalEdgeFamily.adaptive,ite_eq_right empty,scale]
    let k := RationalOriginalEdgeFamily.chooseScale A r a
    change RationalOriginalEdgeFamily.build A q a k = RationalOriginalEdgeFamily.build A r a k
    unfold RationalOriginalEdgeFamily.build
    dsimp only
    rw [demands_congr A same,light,budget]
    congr 1
    funext e
    change max (RationalOriginalEdgeFamily.floor k a) (originalWeight A q e) =
      max (RationalOriginalEdgeFamily.floor k a) (originalWeight A r e)
    rw [arc]

/-- Continue from a preparation already computed on the graph and weights. -/
def familyPrepared (A : Adjacency n) (w : Weights n) (p : Preparation n) :
    RationalWeakFamily.History (Edge n) :=
  if p.preserves then
    RationalOriginalEdgeFamily.adaptive A p.proposed (RationalInstanceEdgeFactor.leastSupported A p.proposed)
  else RationalPrunedEdgeFamily.family A w

def family (A : Adjacency n) (w : Weights n) : RationalWeakFamily.History (Edge n) :=
  familyPrepared A w (prepare A w)

theorem family_reference (A : Adjacency n) (w : Weights n) :
    family A w = RationalBudgetedRescaleEdgeFamily.family A w := by
  unfold family familyPrepared RationalBudgetedRescaleEdgeFamily.family
  dsimp only
  rw [prepare_preserves,RationalBudgetedRescaleEdgeFamily.eligible]
  by_cases accepted : RationalPrunedEdgeFamily.preserves A w (RationalBudgetedRescaleEdgeFamily.rescaled A w) = true
  · simp only [ite_eq_left accepted]
    have same := rescale_weights A w
    change RationalOriginalEdgeFamily.adaptive A (rescale A w).1
        (RationalInstanceEdgeFactor.leastSupported A (rescale A w).1 : ℚ≥0) =
      RationalOriginalEdgeFamily.adaptive A (RationalBudgetedRescaleEdgeFamily.rescaled A w)
        (RationalInstanceEdgeFactor.leastSupported A (RationalBudgetedRescaleEdgeFamily.rescaled A w) : ℚ≥0)
    rw [factor_congr A same]
    exact adaptive_congr A same _
  · simp only [ite_eq_right accepted]

abbrev Draw (n : ℕ) := Option ((Option (Finset (Edge n)) × ℕ) × EncodedSolverBits.Tape)

private def drawHistory (history : RationalWeakFamily.History (Edge n)) (trials : ℕ)
    (tape : List Bool) : Draw n :=
  EncodedSolverBits.run (BinaryFamilySampler.choose history.cuts trials) tape

def drawPrepared (A : Adjacency n) (w : Weights n) (p : Preparation n) (trials : ℕ)
    (tape : List Bool) : Draw n :=
  drawHistory (familyPrepared A w p) trials tape

def draw (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool) : Draw n :=
  drawHistory (family A w) trials tape

theorem draw_reference (A : Adjacency n) (w : Weights n) (trials : ℕ) (tape : List Bool) :
    draw A w trials tape = RationalBudgetedRescaleEdgeFamily.draw A w trials tape := by
  unfold draw drawHistory RationalBudgetedRescaleEdgeFamily.draw
  rw [family_reference]

end DirectedFlowCutGap.MeasuredBudgetRescaleEdgeFamily
