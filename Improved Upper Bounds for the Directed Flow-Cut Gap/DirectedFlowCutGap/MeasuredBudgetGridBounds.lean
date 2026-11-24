import DirectedFlowCutGap.MeasuredDoublingBudgetGrid

/-! Price and mass limits for the geometric budgets, computed using the
actual raw fractions of a resource row. -/
namespace DirectedFlowCutGap.MeasuredBudgetGridBounds

open scoped BigOperators NNRat
open RawNonnegativeRational (Code)
open FractionalCoverRawCore (RawRow RowBounded)
open MeasuredMultiplicityUpdate (ofNat_fits)

private theorem work_mono {a b : ℕ} (h : a ≤ b) :
    BinaryRawRational.budget a ≤ BinaryRawRational.budget b := by
  unfold BinaryRawRational.budget
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 3) 2)

def floorFactor (q : Code) : Code × ℕ :=
  let empty := BinaryRawRational.le q Code.zero
  if empty.1 then (Code.one,empty.2) else
    let small := BinaryRawRational.le q Code.one
    (if small.1 then q else Code.one,empty.2+small.2)

theorem floorFactor_value (q : Code) :
    (floorFactor q).1.value = if 0 < q.value then min 1 q.value else 1 := by
  have test : (BinaryRawRational.le q Code.zero).1 = true ↔ q.value ≤ 0 := by
    rw [BinaryRawRational.le_value,Code.le_eq_true,Code.value_zero]
  have clip : (BinaryRawRational.le q Code.one).1 = true ↔ q.value ≤ 1 := by
    rw [BinaryRawRational.le_value,Code.le_eq_true,Code.value_one]
  by_cases zero : q.value ≤ 0
  · simp only [floorFactor,ite_eq_left (test.mpr zero),ite_eq_right (not_lt_of_ge zero),Code.value_one]
  · simp only [floorFactor,ite_eq_right (fun h => zero (test.mp h)),ite_eq_left (lt_of_not_ge zero)]
    by_cases small : q.value ≤ 1
    · simp only [ite_eq_left (clip.mpr small),min_eq_right small]
    · simp only [ite_eq_right (fun h => small (clip.mp h)),min_eq_left (le_of_lt (lt_of_not_ge small)),
        Code.value_one]

theorem floorFactor_bounds (q : Code) {B : ℕ} (fit : q.Bounded B) :
    (floorFactor q).1.Bounded B ∧ (floorFactor q).2 ≤ 2*BinaryRawRational.budget B := by
  have z := BinaryRawRational.le_paid fit (Code.bounded_mono Code.bounded_zero (Nat.zero_le B))
  have one := Code.bounded_mono Code.bounded_one (Nat.zero_le B)
  have p := BinaryRawRational.le_paid fit one
  dsimp only [floorFactor]
  split
  · exact ⟨one,z.trans (by omega)⟩
  · refine ⟨?_,(Nat.add_le_add z p).trans_eq (by omega)⟩
    dsimp only
    split
    · exact fit
    · exact one

def product : List Code → Code × ℕ
  | [] => (Code.one,0)
  | q::qs =>
    let rest := product qs
    let next := BinaryRawRational.mul q rest.1
    (next.1,rest.2+next.2)

theorem product_value (xs : List Code) : (product xs).1.value = (xs.map Code.value).prod := by
  induction xs with
  | nil => simp [product]
  | cons q qs ih => simp only [product,BinaryRawRational.mul_value,Code.value_mul,List.map_cons,List.prod_cons,ih]

theorem product_bounds (xs : List Code) {B K : ℕ} (fit : ∀ q ∈ xs, q.Bounded B) (size : xs.length ≤ K) :
    (product xs).1.Bounded (xs.length*B) ∧
      (product xs).2 ≤ xs.length*BinaryRawRational.budget (max B (K*B)) := by
  induction xs with
  | nil => simpa only [product,List.length_nil,Nat.zero_mul,le_refl,and_true] using Code.bounded_one
  | cons q qs ih =>
    have a := fit q List.mem_cons_self
    have smaller := (Nat.le_succ qs.length).trans size
    obtain ⟨rest,restWork⟩ := ih (fun v hv => fit v (List.mem_cons_of_mem _ hv)) smaller
    have next := BinaryRawRational.mul_paid (Code.bounded_mono a (le_max_left ..))
      (Code.bounded_mono rest ((Nat.mul_le_mul_right _ smaller).trans (le_max_right ..)))
    constructor
    · simp only [product,BinaryRawRational.mul_value,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm]
      exact Code.bounded_mul a rest
    · simp only [product,List.length_cons,Nat.add_mul,Nat.one_mul]
      exact Nat.add_le_add restWork next

variable {r : ℕ}

private def floorCells (c : RawRow r) : List (Code × ℕ) :=
  List.ofFn fun i => floorFactor (FractionalCoverRawCore.get c i)

def floor (c : RawRow r) : Code × ℕ :=
  let entries := floorCells c
  let p := product (entries.map Prod.fst)
  (p.1,(entries.map Prod.snd).sum+p.2)

theorem floor_value (c : RawRow r) :
    (floor c).1.value = ∏ i : Fin r,
      if 0 < (FractionalCoverRawCore.get c i).value then min 1 (FractionalCoverRawCore.get c i).value else 1 := by
  simp only [floor,product_value,floorCells,List.map_ofFn,Function.comp_def,floorFactor_value,List.prod_ofFn]

def floorWork (r B : ℕ) : ℕ :=
  r*(2*BinaryRawRational.budget B)+r*BinaryRawRational.budget (max B (r*B))

theorem floor_bounds (c : RawRow r) {B : ℕ} (fit : RowBounded c B) :
    (floor c).1.Bounded (r*B) ∧ (floor c).2 ≤ floorWork r B := by
  let items := (floorCells c).map Prod.fst
  have size : items.length = r := by simp [items,floorCells]
  have each (q : Code) (member : q ∈ items) : q.Bounded B := by
    simp only [items,floorCells,List.map_ofFn,Function.comp_def,List.mem_ofFn] at member
    obtain ⟨i,rfl⟩ := member
    exact (floorFactor_bounds _ (fit i)).1
  obtain ⟨fields,work⟩ := product_bounds items each size.le
  rw [size] at fields work
  have charged : ((floorCells c).map Prod.snd).sum ≤ r*(2*BinaryRawRational.budget B) := by
    simp only [floorCells,List.map_ofFn,Function.comp_def,List.sum_ofFn]
    exact (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (floorFactor_bounds _ (fit i)).2).trans_eq (by simp)
  exact ⟨fields,Nat.add_le_add charged work⟩

private theorem sum_value (xs : List Code) :
    (MeasuredMultiplicityForms.sum xs).1.value = (xs.map Code.value).sum := by
  induction xs with
  | nil => simp [MeasuredMultiplicityForms.sum]
  | cons a as ih => simp only [MeasuredMultiplicityForms.sum,BinaryRawRational.add_value,
    Code.value_add,List.map_cons,List.sum_cons,ih]

def ceiling (c : RawRow r) (m : ℕ) : Code × ℕ :=
  let sum := MeasuredMultiplicityForms.sum (List.ofFn (FractionalCoverRawCore.get c))
  let mult := BinaryRawRational.mul (Code.ofNat m) sum.1
  (mult.1,sum.2+mult.2)

theorem ceiling_value (c : RawRow r) (m : ℕ) :
    (ceiling c m).1.value = (m : ℚ≥0)*∑ i : Fin r,(FractionalCoverRawCore.get c i).value := by
  simp only [ceiling,BinaryRawRational.mul_value,Code.value_mul,Code.value_ofNat,
    sum_value,List.map_ofFn,Function.comp_def,List.sum_ofFn]

def ceilingWork (r m B : ℕ) : ℕ :=
  r*BinaryRawRational.budget (r*(B+1))+BinaryRawRational.budget (max m (r*(B+1)))

theorem ceiling_bounds (c : RawRow r) (m : ℕ) {B : ℕ} (fit : RowBounded c B) :
    (ceiling c m).1.Bounded (m+r*(B+1)) ∧ (ceiling c m).2 ≤ ceilingWork r m B := by
  let items := List.ofFn (FractionalCoverRawCore.get c)
  have total (q : Code) (member : q ∈ items) : q.Bounded B := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    exact fit i
  have count : items.length = r := List.length_ofFn
  have stored := FractionalCoverRawCore.sumCodes_bounded items B total
  have fee := MeasuredMultiplicityForms.sum_charge items total count.le
  rw [count] at stored fee
  have values : (MeasuredMultiplicityForms.sum items).1.Bounded (r*(B+1)) := by
    simpa only [MeasuredMultiplicityForms.sum_value] using stored
  have dimension : (Code.ofNat m).Bounded m := ofNat_fits Nat.lt_two_pow_self.le
  have scale := BinaryRawRational.mul_paid (Code.bounded_mono dimension (le_max_left ..))
    (Code.bounded_mono values (le_max_right ..))
  exact ⟨by simpa only [ceiling,BinaryRawRational.mul_value,items] using Code.bounded_mul dimension values,
    Nat.add_le_add fee scale⟩

def capacity (n m p : ℕ) : Code × ℕ :=
  let power := MeasuredSparsityScore.power (Code.ofNat n) p
  let result := BinaryRawRational.mul (Code.ofNat m) power.1
  (result.1,power.2+result.2)

theorem capacity_value (n m p : ℕ) : (capacity n m p).1.value = (m : ℚ≥0)*(n : ℚ≥0)^p := by
  simp only [capacity,BinaryRawRational.mul_value,Code.value_mul,Code.value_ofNat,MeasuredSparsityScore.power_value]

def capacityWork (n m p : ℕ) : ℕ := (p+1)*BinaryRawRational.budget (max m (max n (p*n)))

theorem capacity_bounds (n m p : ℕ) :
    (capacity n m p).1.Bounded (m+p*n) ∧ (capacity n m p).2 ≤ capacityWork n m p := by
  let W := max m (max n (p*n))
  have dim : (Code.ofNat n).Bounded n := ofNat_fits Nat.lt_two_pow_self.le
  have pairs : (Code.ofNat m).Bounded m := ofNat_fits Nat.lt_two_pow_self.le
  have h := MeasuredSparsityScore.power_fits (Code.ofNat n) dim p
  have measured := (MeasuredSparsityScore.power_charge (Code.ofNat n) dim p).trans
    (Nat.mul_le_mul_left p (work_mono (le_max_right m (max n (p*n)))))
  have last := BinaryRawRational.mul_paid (Code.bounded_mono pairs (le_max_left m (max n (p*n))))
    (Code.bounded_mono h ((le_max_right n (p*n)).trans (le_max_right m (max n (p*n)))))
  refine ⟨by simpa only [capacity,BinaryRawRational.mul_value] using Code.bounded_mul pairs h,?_⟩
  change _ ≤ (p+1)*BinaryRawRational.budget W
  rw [Nat.add_mul,Nat.one_mul]
  exact Nat.add_le_add measured last

end DirectedFlowCutGap.MeasuredBudgetGridBounds
