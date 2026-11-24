import DirectedFlowCutGap.MultiplicityCover
import DirectedFlowCutGap.NNRatStoredBounds

/-! Canonical rational widths along the actual multiplicity recurrence.
The update multiplies by a cost- and multiplicity-dependent rational, so
the width of the current weight grows additively at each update. -/
namespace DirectedFlowCutGap.MultiplicityCoverWidths

open scoped BigOperators NNRat
open FractionalCover (Row value value_ofFn objective delta initial)
open MultiplicityCover (Choice Column Oracle State coeff length amount deposit normalized update run)
open RawNonnegativeRational (Code)

def Fits (q : ℚ) (B : ℕ) : Prop :=
  ∃ z : ℚ≥0, (z : ℚ) = q ∧ NNRatStoredBounds.Bounded z B

theorem actual_bits {q : ℚ} {B : ℕ} (fits : Fits q B) :
    q.num.natAbs.size ≤ B+1 ∧ q.den.size ≤ B+1 := by
  obtain ⟨z,rfl,stored⟩ := fits
  change z.num ≤ 2^B ∧ z.den ≤ 2^B at stored
  exact ⟨(Nat.size_le_size stored.1).trans_eq Nat.size_pow,
    (Nat.size_le_size stored.2).trans_eq Nat.size_pow⟩

theorem fits_mono {q : ℚ} {B C : ℕ} (fits : Fits q B) (larger : B ≤ C) : Fits q C := by
  obtain ⟨z,read,stored⟩ := fits
  exact ⟨z,read,NNRatStoredBounds.mono stored larger⟩

theorem fits_code {q : Code} {B : ℕ} (fits : q.Bounded B) : Fits (q.value : ℚ) B :=
  ⟨q.value,rfl,NNRatStoredBounds.value_bounded fits⟩

theorem code_fits (z : ℚ≥0) {B : ℕ} (fits : Fits (z : ℚ) B) : (Code.ofNNRat z).Bounded B := by
  obtain ⟨q,same,stored⟩ := fits
  exact (Subtype.ext same : q = z) ▸ stored

theorem fits_nat {a B : ℕ} (bound : a ≤ 2^B) : Fits (a : ℚ) B := by
  have raw : (Code.ofNat a).Bounded B := ⟨bound,Nat.one_le_pow _ _ (by decide)⟩
  simpa only [Code.value_ofNat,NNRat.coe_natCast] using fits_code raw

private theorem fits_zero : Fits 0 0 := by
  simpa only [Nat.cast_zero] using (fits_nat (a := 0) (B := 0) (by decide))

private theorem fits_one : Fits 1 0 := by
  simpa only [Nat.cast_one] using (fits_nat (a := 1) (B := 0) (by decide))

theorem fits_add {a b : ℚ} {C D : ℕ} (x : Fits a C) (y : Fits b D) : Fits (a+b) (C+D+1) := by
  obtain ⟨r,rfl,rx⟩ := x
  obtain ⟨s,rfl,sy⟩ := y
  exact ⟨r+s,NNRat.coe_add _ _,NNRatStoredBounds.add_bounded rx sy⟩

theorem fits_mul {a b : ℚ} {C D : ℕ} (x : Fits a C) (y : Fits b D) : Fits (a*b) (C+D) := by
  obtain ⟨r,rfl,rx⟩ := x
  obtain ⟨s,rfl,sy⟩ := y
  exact ⟨r*s,NNRat.coe_mul _ _,NNRatStoredBounds.mul_bounded rx sy⟩

theorem fits_div {a b : ℚ} {C D : ℕ} (x : Fits a C) (y : Fits b D) : Fits (a/b) (C+D) := by
  obtain ⟨r,rfl,rx⟩ := x
  obtain ⟨s,rfl,sy⟩ := y
  exact ⟨r/s,NNRat.coe_div _ _,NNRatStoredBounds.div_bounded rx sy⟩

private theorem fits_min {a b : ℚ} {B : ℕ} (x : Fits a B) (y : Fits b B) : Fits (min a b) B := by
  rcases le_total a b with ab | ba
  · rwa [min_eq_left ab]
  · rwa [min_eq_right ba]

theorem fits_sum {ι : Type*} (s : Finset ι) (a : ι → ℚ) (B : ℕ)
    (bounds : ∀ i ∈ s, Fits (a i) B) : Fits (∑ i ∈ s, a i) (s.card*(B+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Finset.card_empty,Nat.zero_mul] using fits_zero
  | @insert i s notIn ih =>
    rw [Finset.sum_insert notIn,Finset.card_insert_of_notMem notIn]
    have x := bounds i (Finset.mem_insert_self ..)
    have xs := ih (fun j found => bounds j (Finset.mem_insert_of_mem found))
    convert fits_add x xs using 1
    ring

variable {r : ℕ}

def RowFits (y : Row r) (B : ℕ) : Prop := ∀ i, Fits (value y i) B

def ColumnFits (p : Column r) (U : ℕ) : Prop := ∀ i, coeff p i ≤ 2^U

private theorem row_mono {y : Row r} {B C : ℕ} (fits : RowFits y B) (larger : B ≤ C) : RowFits y C :=
  fun i => fits_mono (fits i) larger

def weightWidth (r B U k : ℕ) : ℕ := B+2*r+3+k*(2*B+2*U+2)

def normalizedWidth (r U W : ℕ) : ℕ := W+r*(W+U+1)

def objectiveWidth (r B W : ℕ) : ℕ := r*(B+W+1)

def loadWidth (B U k : ℕ) : ℕ := k*(B+2*U+1)

theorem amount_fits (c : Row r) (choice : Choice r) {B U : ℕ}
    (price : RowFits c B) (column : ColumnFits choice.column U) :
    Fits (amount c choice) (B+U) :=
  fits_div (price choice.pivot) (fits_nat (column choice.pivot))

theorem deposit_fits (c : Row r) (choice : Choice r) {B U : ℕ}
    (price : RowFits c B) (column : ColumnFits choice.column U) (i : Fin r) :
    Fits (deposit c choice i) (B+2*U) := by
  unfold deposit
  convert fits_mul (amount_fits c choice price column) (fits_nat (column i)) using 1
  omega

theorem update_fits (c y : Row r) (choice : Choice r) {B U W : ℕ}
    (price : RowFits c B) (column : ColumnFits choice.column U) (row : RowFits y W) :
    RowFits (update c y choice) (W+(2*B+2*U+2)) := by
  intro i
  simp only [update,value_ofFn]
  have two : Fits 2 1 := fits_nat (a := 2) (B := 1) (by decide)
  have product := fits_mul two (price i)
  have increment := fits_div (deposit_fits c choice price column i) product
  convert fits_mul (row i) (fits_add fits_one increment) using 1
  omega

theorem initial_fits (c : Row r) {B : ℕ} (price : RowFits c B) :
    RowFits (initial c) (weightWidth r B 0 0) := by
  intro i
  simp only [initial,value_ofFn,delta,pow_two]
  have two : Fits 2 1 := fits_nat (a := 2) (B := 1) (by decide)
  have three : Fits 3 2 := fits_nat (a := 3) (B := 2) (by decide)
  have dim : Fits (r : ℚ) r := fits_nat Nat.lt_two_pow_self.le
  have small := fits_div two (fits_mul three (fits_mul dim dim))
  convert fits_div small (price i) using 1
  simp only [weightWidth,Nat.zero_mul,Nat.add_zero]
  omega

theorem length_fits (y : Row r) (p : Column r) {U W : ℕ}
    (row : RowFits y W) (column : ColumnFits p U) : Fits (length y p) (r*(W+U+1)) := by
  unfold length
  have h := fits_sum Finset.univ (fun i => (coeff p i : ℚ)*value y i) (U+W)
    (fun i _ => fits_mul (fits_nat (column i)) (row i))
  simpa only [Finset.card_univ,Fintype.card_fin,Nat.add_comm U W] using h

theorem normalized_fits (y : Row r) (p : Column r) {U W : ℕ}
    (row : RowFits y W) (column : ColumnFits p U) : RowFits (normalized y p) (normalizedWidth r U W) := by
  intro i
  simp only [normalized,value_ofFn,normalizedWidth]
  exact fits_div (row i) (length_fits y p row column)

theorem objective_fits (c y : Row r) {B W : ℕ} (price : RowFits c B) (row : RowFits y W) :
    Fits (objective c y) (objectiveWidth r B W) := by
  unfold objective objectiveWidth
  simpa only [Finset.card_univ,Fintype.card_fin] using
    fits_sum Finset.univ (fun i => value c i*value y i) (B+W)
      (fun i _ => fits_mul (price i) (row i))

structure StateFits (s : State r) (B U k : ℕ) : Prop where
  weights : RowFits s.weights (weightWidth r B U k)
  best : RowFits s.best (normalizedWidth r U (weightWidth r B U k))
  bestCost : Fits s.bestCost (objectiveWidth r B (normalizedWidth r U (weightWidth r B U k)))
  total : Fits s.total (loadWidth B U k)
  loads : RowFits s.loads (loadWidth B U k)

private theorem later (s : State r) {B U k t : ℕ} (fits : StateFits s B U k) (time : k ≤ t) :
    StateFits s B U t := by
  have weights : weightWidth r B U k ≤ weightWidth r B U t := by unfold weightWidth; gcongr
  have best : normalizedWidth r U (weightWidth r B U k) ≤ normalizedWidth r U (weightWidth r B U t) := by
    unfold normalizedWidth
    gcongr
  have cost : objectiveWidth r B (normalizedWidth r U (weightWidth r B U k)) ≤
      objectiveWidth r B (normalizedWidth r U (weightWidth r B U t)) := by
    unfold objectiveWidth
    gcongr
  have loads : loadWidth B U k ≤ loadWidth B U t := by unfold loadWidth; gcongr
  exact ⟨row_mono fits.weights weights,row_mono fits.best best,fits_mono fits.bestCost cost,
    fits_mono fits.total loads,row_mono fits.loads loads⟩

theorem run_fits (c : Row r) (oracle : Oracle r) {B U : ℕ} (price : RowFits c B)
    (columns : ∀ y, ColumnFits (oracle y).column U) (k : ℕ) : StateFits (run c oracle k) B U k := by
  induction k with
  | zero =>
    let y := initial c
    let p := (oracle y).column
    have fit : RowFits y (weightWidth r B U 0) := by
      simpa only [y,weightWidth,Nat.zero_mul,Nat.add_zero] using initial_fits c price
    have best := normalized_fits y p fit (columns y)
    refine ⟨fit,best,objective_fits c _ price best,?_ ,?_⟩
    · simpa only [run,MultiplicityCover.start,loadWidth,Nat.zero_mul] using fits_zero
    · intro i
      simpa only [run,MultiplicityCover.start,loadWidth,Nat.zero_mul,value,Vector.getElem_replicate] using fits_zero
  | succ k ih =>
    let s := run c oracle k
    let choice := oracle s.weights
    let w := normalized s.weights choice.column
    let fee := objective c w
    have same : run c oracle (k+1) = MultiplicityCover.step c oracle s := rfl
    rw [same]
    unfold MultiplicityCover.step
    by_cases stop : 1 ≤ objective c s.weights
    · rw [ite_eq_left stop]
      exact later s ih (Nat.le_succ _)
    · rw [ite_eq_right stop]
      have col := columns s.weights
      have weight := update_fits c s.weights choice price col ih.weights
      have growth : weightWidth r B U k+(2*B+2*U+2)=weightWidth r B U (k+1) := by
        unfold weightWidth
        ring
      rw [growth] at weight
      have prev : StateFits s B U (k+1) := later s ih (Nat.le_succ _)
      have candidate := normalized_fits s.weights choice.column prev.weights col
      have candidateCost := objective_fits c w price candidate
      have load : loadWidth B U k+(B+2*U)+1=loadWidth B U (k+1) := by unfold loadWidth; ring
      refine ⟨weight,?_ ,?_ ,?_ ,?_⟩
      · change RowFits (if fee < s.bestCost then w else s.best) _
        split <;> first | exact candidate | exact prev.best
      · exact fits_min candidateCost prev.bestCost
      · have paid := fits_mono (amount_fits c choice price col) (show B+U≤B+2*U by omega)
        rw [← load]
        exact fits_add ih.total paid
      · intro i
        simp only [value_ofFn]
        rw [← load]
        exact fits_add (ih.loads i) (deposit_fits c choice price col i)

theorem solve_fits (c : Row r) (oracle : Oracle r) {B U : ℕ} (price : RowFits c B)
    (columns : ∀ y, ColumnFits (oracle y).column U) :
    StateFits (MultiplicityCover.solve c oracle) B U (3*r^2) :=
  run_fits c oracle price columns _

end DirectedFlowCutGap.MultiplicityCoverWidths
