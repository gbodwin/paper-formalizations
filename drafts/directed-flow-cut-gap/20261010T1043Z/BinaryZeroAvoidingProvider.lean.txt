import DirectedFlowCutGap.BinaryZeroAvoidingSelector
import DirectedFlowCutGap.BinaryApproximatePackingZeros
import DirectedFlowCutGap.BinaryFractionalGraphBounds

/-!
# A concrete monadic zero-avoiding cut provider

The provider is called once on the actual retained penalized binary table. Its
valid-or-none mask result, operation count, physical failure flag and bit-valued
trial/consumption metadata are retained. The selected final mask is determined
by the literal binary selector. Only then is its bottleneck recomputed by the
actual binary scan on the ORIGINAL input capacities.

Support validity and empty-not-valid imply that this final mask is nonempty.
Thus the scan's `none` branch is impossible by the existing binary-to-rational
refinement and bottleneck-existence theorem; no arbitrary default index is used.
The resulting erased structural certificate supplies the actual packing
`SafeAnswer` interface, including its auxiliary-capacity version.

Physical failure metadata is copied verbatim and is not identified with a
violation of an alpha-cost bound. Alpha occurs only in successful-cost proofs.
The graph-resource indexing, original cut provider and its stochastic quality
law remain explicit. Imports include pending packing and graph-bound drafts;
this module is not an assertion of their verification status.
-/

namespace DirectedFlowCutGap.BinaryZeroAvoidingProvider

open scoped BigOperators NNRat
open BinaryRational BinaryFractionalRows BinaryApproximatePacking
open BinaryApproximatePackingZeros ZeroAvoidingSelector

variable {m : ℕ}

abbrev Mask (m : ℕ) := Vector Bool m

/-- Validity is structural and erased. The physical failure flag is independent
of both the option tag and any proof-level approximation event. -/
structure CutAnswer (columns : Set (FractionalCover.Column m)) where
  mask : Option (Mask m)
  operations : ℕ
  failed : Bool
  trials : BinaryArithmetic.Bits
  consumed : BinaryArithmetic.Bits
  valid : ∀ x, mask = some x → column x ∈ columns

abbrev CutProvider (M : Type → Type) (columns : Set (FractionalCover.Column m)) :=
  Row m → M (CutAnswer columns)

def SupportValid (w : Row m) (columns : Set (FractionalCover.Column m)) : Prop :=
  positiveSupport (BinaryZeroAvoidingSelector.tableValue w) ∈ columns

/-- Every actual return, including the explicit `none` fallback, is an original
valid zero-free column. This statement has no quality or failure-flag premise. -/
theorem selected_valid (w c : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (a : CutAnswer columns) :
    column (BinaryZeroAvoidingSelector.select (BinaryZeroAvoidingSelector.prepare w c)
      (a.mask, a.operations)).1 ∈ zeroFreeColumns w columns := by
  have h := Raw.select_valid_avoids (decodeRow w) (decodeRow c)
    (a.mask, a.operations) (fun S => S ∈ columns) hS
    (fun x hx => a.valid x hx)
  rw [← BinaryZeroAvoidingSelector.select_refines_raw w c (a.mask, a.operations)] at h
  refine ⟨h.1, ?_⟩
  intro i hi
  have hp : 0 < BinaryZeroAvoidingSelector.tableValue w i := h.2 i hi
  rw [BinaryZeroAvoidingSelector.tableValue_apply] at hp
  exact_mod_cast hp

theorem selected_nonempty (w c : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (a : CutAnswer columns) :
    (column (BinaryZeroAvoidingSelector.select (BinaryZeroAvoidingSelector.prepare w c)
      (a.mask, a.operations)).1).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  have hv := (selected_valid w c columns hS a).1
  rw [he] at hv
  exact hempty hv

/-- The actual scan attains a bottleneck for every nonempty final mask. Its
capacity input is the original row, independently of the penalized query. -/
theorem bottleneck_exists (w : Row m) (x : Mask m) (hx : (column x).Nonempty) :
    ∃ i, (BinaryFractionalGraphOracle.bottleneck w x).1 = some i := by
  rw [BinaryFractionalGraphOracle.bottleneck_decode,
    FractionalCoverRawGraph.bottleneck_refines]
  exact FractionalCoverGraphOracle.bottleneck_exists (capacities w) (column x) hx

theorem bottleneck_spec (w : Row m) (x : Mask m) (i : Fin m)
    (hi : (BinaryFractionalGraphOracle.bottleneck w x).1 = some i) :
    i ∈ column x ∧ ∀ j ∈ column x,
      FractionalCover.value (capacities w) i ≤ FractionalCover.value (capacities w) j := by
  rw [BinaryFractionalGraphOracle.bottleneck_decode,
    FractionalCoverRawGraph.bottleneck_refines] at hi
  exact FractionalCoverGraphOracle.bottleneck_spec (capacities w) (column x) hi

/-- All fields other than the retained answer are proposition-valued. This
certificate records the actual selected mask, actual scan result and metadata;
it is not an alternative execution or an assumed favorable transcript. -/
structure Completion (w : Row m) (columns : Set (FractionalCover.Column m))
    (q : BinaryZeroAvoidingSelector.Prepared m) (a : CutAnswer columns) where
  answer : Answer m
  safe : SafeChoice w (zeroFreeColumns w columns) answer.choice
  mask_eq : answer.choice.mask = (BinaryZeroAvoidingSelector.select q (a.mask, a.operations)).1
  bottleneck_eq :
    (BinaryFractionalGraphOracle.bottleneck w
      (BinaryZeroAvoidingSelector.select q (a.mask, a.operations)).1).1 =
        some answer.choice.bottleneck
  operations_eq : answer.operations = q.work +
    (BinaryZeroAvoidingSelector.select q (a.mask, a.operations)).2 +
    (BinaryFractionalGraphOracle.bottleneck w
      (BinaryZeroAvoidingSelector.select q (a.mask, a.operations)).1).2 + 20
  failed_eq : answer.failed = a.failed
  trials_eq : answer.trials = a.trials
  consumed_eq : answer.consumed = a.consumed

/-- The prepared table is supplied once by the monadic entry point. `hq` is an
erased equality certificate; this function never reruns preparation. Selection
and the original-capacity bottleneck scan are each evaluated once. The fixed
20-operation allowance pays branch and result-record structural work. -/
def finish (w c : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (q : BinaryZeroAvoidingSelector.Prepared m) (hq : q = BinaryZeroAvoidingSelector.prepare w c)
    (a : CutAnswer columns) : Completion w columns q a :=
  let selected := BinaryZeroAvoidingSelector.select q (a.mask, a.operations)
  let b := BinaryFractionalGraphOracle.bottleneck w selected.1
  have hv : column selected.1 ∈ zeroFreeColumns w columns := by
    dsimp only [selected]
    rw [hq]
    exact selected_valid w c columns hS a
  have hn : (column selected.1).Nonempty := by
    dsimp only [selected]
    rw [hq]
    exact selected_nonempty w c columns hS hempty a
  have hex : ∃ i, b.1 = some i := bottleneck_exists w selected.1 hn
  match hb : b.1 with
  | none => False.elim (by obtain ⟨i, hi⟩ := hex; rw [hb] at hi; cases hi)
  | some i =>
      { answer :=
          { choice := ⟨selected.1, i⟩
            operations := q.work + selected.2 + b.2 + 20
            failed := a.failed
            trials := a.trials
            consumed := a.consumed }
        safe := ⟨hv, bottleneck_spec w selected.1 i hb⟩
        mask_eq := rfl
        bottleneck_eq := hb
        operations_eq := rfl
        failed_eq := rfl
        trials_eq := rfl
        consumed_eq := rfl }

def Completion.asSafe {w : Row m} {columns : Set (FractionalCover.Column m)}
    {q : BinaryZeroAvoidingSelector.Prepared m} {a : CutAnswer columns}
    (r : Completion w columns q a) : SafeAnswer w (zeroFreeColumns w columns) :=
  ⟨r.answer, r.safe⟩

/-- One monadic provider call at the actual penalized table, followed by the
literal final-mask selection and fresh original-capacity bottleneck scan. -/
def provider {M : Type → Type} [Monad M] (w : Row m)
    (columns : Set (FractionalCover.Column m)) (hS : SupportValid w columns)
    (hempty : (∅ : FractionalCover.Column m) ∉ columns) (draw : CutProvider M columns) :
    Oracle M w (zeroFreeColumns w columns) := fun c => do
  let q := BinaryZeroAvoidingSelector.prepare w c
  let a ← draw q.costs
  let r := finish w c columns hS hempty q rfl a
  pure r.asSafe

theorem provider_equation {M : Type → Type} [Monad M] (w : Row m)
    (columns : Set (FractionalCover.Column m)) (hS : SupportValid w columns)
    (hempty : (∅ : FractionalCover.Column m) ∉ columns) (draw : CutProvider M columns)
    (c : Row m) :
    provider w columns hS hempty draw c = (do
      let q := BinaryZeroAvoidingSelector.prepare w c
      let a ← draw q.costs
      let r := finish w c columns hS hempty q rfl a
      pure r.asSafe) := rfl

/-- Only the erased safety proof changes. Original capacities still supplied
the actual bottleneck; the answer and every metadata field are unchanged. -/
def Completion.asAuxiliary {w : Row m} {columns : Set (FractionalCover.Column m)}
    {q : BinaryZeroAvoidingSelector.Prepared m} {a : CutAnswer columns}
    (r : Completion w columns q a) :
    SafeAnswer (auxiliary w) (zeroFreeColumns w columns) :=
  ⟨r.answer, safe_auxiliary w columns r.answer.choice r.safe⟩

def auxiliaryProvider {M : Type → Type} [Monad M] (w : Row m)
    (columns : Set (FractionalCover.Column m)) (hS : SupportValid w columns)
    (hempty : (∅ : FractionalCover.Column m) ∉ columns) (draw : CutProvider M columns) :
    Oracle M (auxiliary w) (zeroFreeColumns w columns) := fun c => do
  let q := BinaryZeroAvoidingSelector.prepare w c
  let a ← draw q.costs
  let r := finish w c columns hS hempty q rfl a
  pure r.asAuxiliary

theorem auxiliaryProvider_equation {M : Type → Type} [Monad M] (w : Row m)
    (columns : Set (FractionalCover.Column m)) (hS : SupportValid w columns)
    (hempty : (∅ : FractionalCover.Column m) ∉ columns) (draw : CutProvider M columns)
    (c : Row m) :
    auxiliaryProvider w columns hS hempty draw c = (do
      let q := BinaryZeroAvoidingSelector.prepare w c
      let a ← draw q.costs
      let r := finish w c columns hS hempty q rfl a
      pure r.asAuxiliary) := rfl

theorem Completion.amount_positive {w : Row m} {columns : Set (FractionalCover.Column m)}
    {q : BinaryZeroAvoidingSelector.Prepared m} {a : CutAnswer columns}
    (r : Completion w columns q a) :
    0 < (decode (get w r.answer.choice.bottleneck)).value :=
  r.safe.1.2 _ r.safe.2.1

/-- The actual retained auxiliary amount is the original input Fraction,
including its original numerator and denominator padding. -/
theorem Completion.amount_original {w : Row m} {columns : Set (FractionalCover.Column m)}
    {q : BinaryZeroAvoidingSelector.Prepared m} {a : CutAnswer columns}
    (r : Completion w columns q a) :
    get (auxiliary w) r.answer.choice.bottleneck = get w r.answer.choice.bottleneck :=
  BinaryPositiveCapacities.preserves_positive w _ r.amount_positive

/-- This theorem refers to the actual successful mask and its actual queried
costs. It has no premise about the physical failure flag, trial count or bits. -/
theorem Completion.preserves_factor {w c : Row m} {columns : Set (FractionalCover.Column m)}
    {q : BinaryZeroAvoidingSelector.Prepared m} {a : CutAnswer columns}
    (r : Completion w columns q a) (hq : q = BinaryZeroAvoidingSelector.prepare w c)
    (x : Mask m) (hx : a.mask = some x) (α : ℝ)
    (hcost : (∑ i ∈ column x, BinaryZeroAvoidingSelector.tableValue q.costs i) ≤
      α * mwPotential (BinaryZeroAvoidingSelector.tableValue w)
        (BinaryZeroAvoidingSelector.tableValue q.costs)) :
    (∑ i ∈ (BinaryFractionalCore.decodeChoice r.answer.choice).column,
      BinaryZeroAvoidingSelector.tableValue c i) ≤
        α * mwPotential (BinaryZeroAvoidingSelector.tableValue w)
          (BinaryZeroAvoidingSelector.tableValue c) := by
  have he : BinaryZeroAvoidingSelector.tableValue (BinaryZeroAvoidingSelector.prepare w c).costs =
      penalty (positiveSupport (BinaryZeroAvoidingSelector.tableValue w))
        (BinaryZeroAvoidingSelector.tableValue c) :=
    funext (BinaryZeroAvoidingSelector.prepare_cost w c)
  rw [hq, BinaryZeroAvoidingSelector.prepare_potential, he] at hcost
  change (∑ i ∈ Raw.cut r.answer.choice.mask, BinaryZeroAvoidingSelector.tableValue c i) ≤ _
  rw [r.mask_eq, hq, hx, BinaryZeroAvoidingSelector.select_some_cut]
  exact (choose_cost_le _ _ (BinaryZeroAvoidingSelector.tableValue_nonneg c) _).trans hcost

theorem select_operations_add (q : BinaryZeroAvoidingSelector.Prepared m)
    (x : Option (Mask m)) (operations : ℕ) :
    (BinaryZeroAvoidingSelector.select q (x, operations)).2 =
      operations + (BinaryZeroAvoidingSelector.select q (x, 0)).2 := by
  cases x with
  | none => rfl
  | some x =>
      simp only [BinaryZeroAvoidingSelector.select]
      omega

/-- The original provider charge is included exactly once, even on a physical
failure or `none` fallback; every wrapper operation is added to that charge. -/
theorem Completion.provider_charge_once {w : Row m} {columns : Set (FractionalCover.Column m)}
    {q : BinaryZeroAvoidingSelector.Prepared m} {a : CutAnswer columns}
    (r : Completion w columns q a) :
    r.answer.operations = a.operations + q.work +
      (BinaryZeroAvoidingSelector.select q (a.mask, 0)).2 +
      (BinaryFractionalGraphOracle.bottleneck w
        (BinaryZeroAvoidingSelector.select q (a.mask, a.operations)).1).2 + 20 := by
  rw [r.operations_eq, select_operations_add]
  omega

def overheadBound (m Bw Bc : ℕ) : ℕ :=
  BinaryZeroAvoidingSelector.prepareBound m Bw Bc +
    BinaryZeroAvoidingSelector.selectBound m Bc +
    BinaryFractionalGraphBounds.bottleneckBound m Bw + 20

/-- Both branches include the actual original-input bottleneck scan. Its width
is the original capacity width Bw, not the penalized-query width. -/
theorem Completion.charge {w c : Row m} {columns : Set (FractionalCover.Column m)}
    {q : BinaryZeroAvoidingSelector.Prepared m} {a : CutAnswer columns}
    (r : Completion w columns q a) (hq : q = BinaryZeroAvoidingSelector.prepare w c)
    (Bw Bc : ℕ) (hw : BinaryZeroAvoidingSelector.RowStored w Bw)
    (hc : BinaryZeroAvoidingSelector.RowStored c Bc) :
    r.answer.operations ≤ a.operations + overheadBound m Bw Bc := by
  have hp : q.work ≤ BinaryZeroAvoidingSelector.prepareBound m Bw Bc := by
    rw [hq]
    exact BinaryZeroAvoidingSelector.prepare_charge w c Bw Bc hw hc
  have hs : (BinaryZeroAvoidingSelector.select q (a.mask, a.operations)).2 ≤
      a.operations + BinaryZeroAvoidingSelector.selectBound m Bc := by
    rw [hq]
    exact BinaryZeroAvoidingSelector.select_charge w c (a.mask, a.operations) Bc hc
  have hb := BinaryFractionalGraphBounds.bottleneck_charge w hw
    (BinaryZeroAvoidingSelector.select q (a.mask, a.operations)).1
  rw [r.operations_eq]
  unfold overheadBound
  omega

end DirectedFlowCutGap.BinaryZeroAvoidingProvider
