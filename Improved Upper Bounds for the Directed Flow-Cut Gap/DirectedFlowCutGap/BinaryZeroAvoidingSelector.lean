import DirectedFlowCutGap.ZeroAvoidingSelector
import DirectedFlowCutGap.BinaryFractionalRows

/-!
# Binary realization of positive-support zero avoidance

The support scan calls the actual binary numerator-zero test. Both mask costs
call `BinaryFractionalRows.length`; the penalty uses binary rational addition,
and the candidate/support comparison uses the actual binary cross-products.
The current costs, support budget and penalized table are retained once. A run
evaluates its oracle once and carries its returned charge through both branches.
No executable value computation decodes binary fields to natural arithmetic.

The output mask refines the raw selector in `ZeroAvoidingSelector`. Only the
real-valued cost semantics of the two independently implemented sum scans are
identified; equality of their unreduced stored records is not assumed.

Charges use the existing Boolean/list and charged-tabulation structural model.
Array/address and primitive-body interpretations remain those of the imported
modules. This is not a native compiler/allocator or machine-instruction claim.
The original-graph resource indexing and oracle validity/probability contracts
remain explicit. The imported `ZeroAvoidingSelector` is a frozen uncompiled
dependency at drafting time; this file does not upgrade its verification state.
-/

namespace DirectedFlowCutGap.BinaryZeroAvoidingSelector

open scoped BigOperators NNReal NNRat
open BinaryRational BinaryFractionalRows EncodedRoundingInput ZeroAvoidingSelector

abbrev Mask (m : ℕ) := Vector Bool m

variable {m : ℕ}

/-- Proof-only denotation; no executable constructor below calls this map. -/
noncomputable def tableValue (c : Row m) : Fin m → ℝ := Raw.value (decodeRow c)

@[simp] theorem tableValue_apply (c : Row m) (i : Fin m) :
    tableValue c i = ((decode (BinaryFractionalRows.get c i)).value : ℝ) := by
  simp [tableValue, Raw.value, decodeRow, BinaryFractionalRows.get]

theorem tableValue_nonneg (c : Row m) (i : Fin m) : 0 ≤ tableValue c i := by
  rw [tableValue_apply]
  positivity

private theorem raw_sum_value (xs : List RawNonnegativeRational.Code) :
    (FractionalCoverRawCore.sumCodes xs).value =
      (xs.map RawNonnegativeRational.Code.value).sum := by
  induction xs <;> simp [FractionalCoverRawCore.sumCodes, *]

/-- The actual binary mask-cost scan has exactly the finite cut-cost meaning. -/
theorem length_value (c : Row m) (x : Mask m) :
    ((decode (BinaryFractionalRows.length c x).1).value : ℝ) =
      ∑ i ∈ Raw.cut x, tableValue c i := by
  rw [length_decode]
  simp only [FractionalCoverRawCore.lengthCode, raw_sum_value,
    List.map_ofFn, List.sum_ofFn, NNRat.cast_sum, Raw.cut, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x[i.val] <;>
    simp [column, tableValue, Raw.value, FractionalCoverRawCore.get, decodeRow, BinaryFractionalRows.get, hx]

private theorem nonzero_decode (a : Fraction) :
    (!(BinaryRational.isZero a).1) = decide ((decode a).num ≠ 0) := by
  cases h : (BinaryRational.isZero a).1 with
  | false =>
      have hn : (decode a).num ≠ 0 := fun hz =>
        Bool.false_ne_true (h.symm.trans ((isZero_decode a).mpr hz))
      simp [hn]
  | true =>
      have hz : (decode a).num = 0 := (isZero_decode a).mp h
      simp [hz]

/-- Actual numerator-bit scan, including padded zero numerators. -/
def support (w : Row m) : Mask m × ℕ :=
  tabulate fun i : Fin m =>
    let z := BinaryRational.isZero (BinaryFractionalRows.get w i)
    (!z.1, z.2 + 6)

@[simp] theorem support_get (w : Row m) (i : Fin m) :
    (support w).1[i.val] = decide ((decode (BinaryFractionalRows.get w i)).num ≠ 0) := by
  simp only [support, tabulate_get]
  exact nonzero_decode (BinaryFractionalRows.get w i)

/-- The binary and raw scans retain the same support mask. -/
theorem support_refines_raw (w : Row m) :
    (support w).1 = (Raw.support (decodeRow w)).1 := by
  apply Vector.ext
  intro i hi
  change (support w).1[(⟨i, hi⟩ : Fin m).val] =
    (Raw.support (decodeRow w)).1[(⟨i, hi⟩ : Fin m).val]
  rw [support_get, Raw.support_get]
  change decide ((decode (BinaryFractionalRows.get w (⟨i, hi⟩ : Fin m))).num ≠ 0) =
    decide ((FractionalCoverRawCore.get (decodeRow w) (⟨i, hi⟩ : Fin m)).num ≠ 0)
  rw [decode_get]

theorem support_correct (w : Row m) :
    Raw.cut (support w).1 = positiveSupport (tableValue w) := by
  rw [support_refines_raw, Raw.support_correct]
  rfl

structure Prepared (m : ℕ) where
  fallback : Mask m
  costs : Row m
  budget : Fraction
  work : ℕ

/-- Retain the original-support cost and add binary one. Alpha is absent from
every input and branch of this constructor. -/
def prepare (w c : Row m) : Prepared m :=
  let s := support w
  let b := BinaryFractionalRows.length c s.1
  let z := BinaryRational.add b.1 one
  let d := tabulate fun i : Fin m => (if s.1[i.val] then BinaryFractionalRows.get c i else z.1, 6)
  ⟨s.1, d.1, b.1, s.2 + b.2 + z.2 + d.2 + 8⟩

@[simp] theorem prepare_get (w c : Row m) (i : Fin m) :
    BinaryFractionalRows.get (prepare w c).costs i =
      if (support w).1[i.val] then BinaryFractionalRows.get c i else
        (BinaryRational.add (BinaryFractionalRows.length c (support w).1).1 one).1 := by
  simp [prepare, BinaryFractionalRows.get]

theorem prepare_budget (w c : Row m) :
    ((decode (prepare w c).budget).value : ℝ) =
      ∑ i ∈ positiveSupport (tableValue w), tableValue c i := by
  simpa only [prepare, support_correct] using length_value c (support w).1

theorem prepare_cost (w c : Row m) (i : Fin m) :
    tableValue (prepare w c).costs i =
      penalty (positiveSupport (tableValue w)) (tableValue c) i := by
  classical
  have hs : (support w).1[i.val] = true ↔ i ∈ positiveSupport (tableValue w) := by
    rw [← support_correct w, Raw.mem_cut]
  have hb := prepare_budget w c
  change ((decode (BinaryFractionalRows.length c (support w).1).1).value : ℝ) = _ at hb
  rw [tableValue_apply, prepare_get]
  by_cases hi : (support w).1[i.val] = true
  · simp [hi, penalty, hs.mp hi]
  · have hn : i ∉ positiveSupport (tableValue w) := fun h => hi (hs.mpr h)
    simp [hi, penalty, hn, hb]

/-- Exact queried-cost semantics, including preservation of the original
weighted potential. No executable step calls this real-valued function. -/
theorem prepare_potential (w c : Row m) :
    mwPotential (tableValue w) (tableValue (prepare w c).costs) =
      mwPotential (tableValue w) (tableValue c) := by
  have he : tableValue (prepare w c).costs =
      penalty (positiveSupport (tableValue w)) (tableValue c) := funext (prepare_cost w c)
  rw [he]
  exact penalty_potential _ _ (tableValue_nonneg w)

/-- Use the candidate's actual binary mask-cost scan and compare against the
retained support budget. The explicit failure branch returns support. -/
def select (q : Prepared m) (o : Option (Mask m) × ℕ) : Mask m × ℕ :=
  match o.1 with
  | none => (q.fallback, o.2 + 4)
  | some x =>
      let c := BinaryFractionalRows.length q.costs x
      let b := BinaryRational.le c.1 q.budget
      (if b.1 then x else q.fallback, o.2 + c.2 + b.2 + 8)

@[simp] theorem select_none (q : Prepared m) (work : ℕ) :
    (select q (none, work)).1 = q.fallback := rfl

theorem select_some_cut (w c : Row m) (x : Mask m) (work : ℕ) :
    Raw.cut (select (prepare w c) (some x, work)).1 =
      choose (positiveSupport (tableValue w)) (tableValue c) (Raw.cut x) := by
  classical
  let q := prepare w c
  have hf : Raw.cut q.fallback = positiveSupport (tableValue w) := support_correct w
  have hb : (BinaryRational.le (BinaryFractionalRows.length q.costs x).1 q.budget).1 = true ↔
      (∑ i ∈ Raw.cut x, penalty (positiveSupport (tableValue w)) (tableValue c) i) ≤
        ∑ i ∈ positiveSupport (tableValue w), tableValue c i := by
    rw [le_decode, RawNonnegativeRational.Code.le_eq_true]
    have he : (decode (BinaryFractionalRows.length q.costs x).1).value ≤
        (decode q.budget).value ↔
        ((decode (BinaryFractionalRows.length q.costs x).1).value : ℝ) ≤
          ((decode q.budget).value : ℝ) := by norm_cast
    rw [he, length_value, prepare_budget]
    simp only [q, prepare_cost]
  change Raw.cut (if (BinaryRational.le (BinaryFractionalRows.length q.costs x).1
    q.budget).1 then x else q.fallback) = _
  unfold choose
  by_cases h : (BinaryRational.le (BinaryFractionalRows.length q.costs x).1 q.budget).1 = true
  · rw [ite_eq_left h, ite_eq_left (hb.mp h)]
  · have hn := fun hle => h (hb.mpr hle)
    rw [ite_eq_right h, ite_eq_right hn]
    exact hf

private theorem cut_injective : Function.Injective (Raw.cut (m := m)) := by
  intro x y h
  apply Vector.ext
  intro i hi
  apply Bool.eq_iff_iff.mpr
  have hm := Iff.of_eq (congrArg (fun S : Finset (Fin m) => (⟨i, hi⟩ : Fin m) ∈ S) h)
  simpa only [Raw.mem_cut] using hm

/-- Exact output-mask refinement in both branches. This proof does not replace
either binary cost scan with an assumed raw charge. -/
theorem select_refines_raw (w c : Row m) (o : Option (Mask m) × ℕ) :
    (select (prepare w c) o).1 =
      (Raw.select (Raw.prepare (decodeRow w) (decodeRow c)) o).1 := by
  rcases o with ⟨o, work⟩
  cases o with
  | none => exact support_refines_raw w
  | some x =>
      apply cut_injective
      rw [select_some_cut, Raw.select_some_refines]
      rfl

/-- Evaluate the oracle once on the actual retained binary table. -/
def run (w c : Row m) (oracle : Row m → Option (Mask m) × ℕ) : Mask m × ℕ :=
  let q := prepare w c
  let o := oracle q.costs
  let r := select q o
  (r.1, q.work + r.2 + 4)

theorem run_refines_raw_select (w c : Row m) (oracle : Row m → Option (Mask m) × ℕ) :
    (run w c oracle).1 =
      (Raw.select (Raw.prepare (decodeRow w) (decodeRow c))
        (oracle (prepare w c).costs)).1 := select_refines_raw w c _

theorem run_valid_avoids (w c : Row m) (oracle : Row m → Option (Mask m) × ℕ)
    (P : Finset (Fin m) → Prop) (hS : P (positiveSupport (tableValue w)))
    (hvalid : ∀ x, (oracle (prepare w c).costs).1 = some x → P (Raw.cut x)) :
    P (Raw.cut (run w c oracle).1) ∧
      ∀ i ∈ Raw.cut (run w c oracle).1, 0 < tableValue w i := by
  rw [run_refines_raw_select]
  exact Raw.select_valid_avoids (decodeRow w) (decodeRow c) _ P hS hvalid

/-- A real factor occurs only in this specification. Failed queries are not
promoted to cost-guaranteed calls; validity is a separate contract above. -/
theorem run_preserves_factor (w c : Row m) (oracle : Row m → Option (Mask m) × ℕ)
    (x : Mask m) (α : ℝ) (hx : (oracle (prepare w c).costs).1 = some x)
    (hcost : (∑ i ∈ Raw.cut x, tableValue (prepare w c).costs i) ≤
      α * mwPotential (tableValue w) (tableValue (prepare w c).costs)) :
    (∑ i ∈ Raw.cut (run w c oracle).1, tableValue c i) ≤
      α * mwPotential (tableValue w) (tableValue c) := by
  have he : tableValue (prepare w c).costs =
      penalty (positiveSupport (tableValue w)) (tableValue c) := funext (prepare_cost w c)
  rw [prepare_potential, he] at hcost
  rcases ho : oracle (prepare w c).costs with ⟨result, work⟩
  have hr : result = some x := by simpa only [ho] using hx
  subst result
  change (∑ i ∈ Raw.cut (select (prepare w c) (oracle (prepare w c).costs)).1,
    tableValue c i) ≤ _
  rw [ho, select_some_cut]
  exact (choose_cost_le _ _ (tableValue_nonneg c) _).trans hcost

/-! ## Stored widths and actual primitive charges -/

def RowStored (c : Row m) (B : ℕ) : Prop := ∀ i, StoredBounded (BinaryFractionalRows.get c i) B

private theorem stored_mono {a : Fraction} {A B : ℕ}
    (ha : StoredBounded a A) (hAB : A ≤ B) : StoredBounded a B :=
  ⟨ha.1.trans hAB, ha.2.trans hAB⟩

def budgetWidth (m B : ℕ) : ℕ := m*(B+1)+1

def queryWidth (m B : ℕ) : ℕ := B + budgetWidth m B + 2

def comparisonWidth (m B : ℕ) : ℕ :=
  budgetWidth m B + budgetWidth m (queryWidth m B)

theorem prepare_stored (w c : Row m) (B : ℕ) (hc : RowStored c B) :
    StoredBounded (prepare w c).budget (budgetWidth m B) ∧
      RowStored (prepare w c).costs (queryWidth m B) := by
  have hb := length_stored c (support w).1 B hc
  have hone : (decode one).Bounded 0 := by
    simpa only [decode_one] using RawNonnegativeRational.Code.bounded_one
  have hz := add_stored_bounded (stored_raw_bound hb) hone
  constructor
  · exact hb
  · intro i
    rw [prepare_get]
    split
    · exact stored_mono (hc i) (by unfold queryWidth; omega)
    · exact stored_mono hz (by unfold queryWidth budgetWidth; omega)

theorem candidate_stored (w c : Row m) (x : Mask m) (B : ℕ) (hc : RowStored c B) :
    StoredBounded (BinaryFractionalRows.length (prepare w c).costs x).1
      (budgetWidth m (queryWidth m B)) :=
  length_stored _ x _ (prepare_stored w c B hc).2

/-- This charges the supplied weight padding, even for a zero numerator. -/
def supportBound (m B : ℕ) : ℕ := m*(4*(B+1)+6)+arrayBound m

theorem support_charge (w : Row m) (B : ℕ) (hw : RowStored w B) :
    (support w).2 ≤ supportBound m B := by
  exact tabulate_bound _ _ (fun i => Nat.add_le_add_right (isZero_charge (hw i)) 6)

def prepareBound (m Bw Bc : ℕ) : ℕ :=
  supportBound m Bw + lengthBound m Bc + 2048*(budgetWidth m Bc+1)^2 +
    (6*m+arrayBound m) + 8

theorem prepare_charge (w c : Row m) (Bw Bc : ℕ)
    (hw : RowStored w Bw) (hc : RowStored c Bc) :
    (prepare w c).work ≤ prepareBound m Bw Bc := by
  have hs := support_charge w Bw hw
  have hb := length_charge c (support w).1 Bc hc
  have hbs := length_stored c (support w).1 Bc hc
  have hone : StoredBounded one (budgetWidth m Bc) := by
    simp [StoredBounded, one, budgetWidth]
  have ha := add_charge hbs hone
  have hd := tabulate_bound (fun i : Fin m =>
    (if (support w).1[i.val] then BinaryFractionalRows.get c i else
      (BinaryRational.add (BinaryFractionalRows.length c (support w).1).1 one).1, 6))
      6 (fun _ => le_rfl)
  simp only [prepare, prepareBound, budgetWidth]
  omega

/-- Candidate scan plus comparison. Both budgets cover all possible masks,
including invalid or over-budget candidates, before any semantic oracle claim. -/
def selectBound (m B : ℕ) : ℕ :=
  lengthBound m (queryWidth m B) + 2048*(comparisonWidth m B+1)^2 + 8

theorem select_charge (w c : Row m) (o : Option (Mask m) × ℕ) (B : ℕ)
    (hc : RowStored c B) :
    (select (prepare w c) o).2 ≤ o.2 + selectBound m B := by
  have hq := prepare_stored w c B hc
  cases ho : o.1 with
  | none => simp [select, ho, selectBound]
  | some x =>
      have hs := length_charge (prepare w c).costs x (queryWidth m B) hq.2
      have hcs := candidate_stored w c x B hc
      have ha : StoredBounded
          (BinaryFractionalRows.length (prepare w c).costs x).1 (comparisonWidth m B) :=
        stored_mono hcs (by unfold comparisonWidth; omega)
      have hb : StoredBounded (prepare w c).budget (comparisonWidth m B) :=
        stored_mono hq.1 (by unfold comparisonWidth; omega)
      have hl := le_charge ha hb
      simp only [select, ho, selectBound]
      omega

/-- An explicit polynomial in resource count and supplied weight/cost bit
lengths. Only additions, products and fixed squares occur in its definition. -/
def runBound (m Bw Bc : ℕ) : ℕ := prepareBound m Bw Bc + selectBound m Bc + 4

theorem run_charge (w c : Row m) (oracle : Row m → Option (Mask m) × ℕ)
    (Bw Bc : ℕ) (hw : RowStored w Bw) (hc : RowStored c Bc) :
    (run w c oracle).2 ≤ (oracle (prepare w c).costs).2 + runBound m Bw Bc := by
  have hp := prepare_charge w c Bw Bc hw hc
  have hs := select_charge w c (oracle (prepare w c).costs) Bc hc
  simp only [run, runBound]
  omega

end DirectedFlowCutGap.BinaryZeroAvoidingSelector
