import DirectedFlowCutGap.BinaryFractionalStepCost
import DirectedFlowCutGap.BinaryRationalCeiling
import DirectedFlowCutGap.EncodedUnitCostReplication

/-!
# Binary scalar parameters for the existing weighted cost-replication reduction

These bodies refine the raw reduction's exact unreduced aggregate fields,
normalization, and max-one ceiling counts. They use existing Boolean-list
rational arithmetic and long division. The caller retains the aggregate once,
checks its objective zero flag, and invokes normalization only in the positive
branch. Graph preparation, clone materialization and the monadic rounding entry
remain separate joins; no new graph or substitute approximation algorithm is
introduced here.

N is the CURRENT prepared graph's row dimension. It is not silently identified
with original graph n or with the n² edge-resource dimension. The later port
adapter must supply the existing PreparedBounds n and retain the original W.
-/
namespace DirectedFlowCutGap.BinaryUnitCostParameters
open BinaryArithmetic BinaryRational BinaryFractionalRows BinaryFractionalCanonical
open EncodedRoundingInput

variable {N : ℕ}

structure Totals where
  weight : Fraction
  objective : Fraction
  operations : ℕ

/-- Exactly the raw reduction's suffix-first summation and multiplication order. -/
def scan (w c : Row N) : List (Fin N) → Totals
  | [] => ⟨zero,zero,1⟩
  | i::is =>
      let r := scan w c is
      let p := BinaryRational.mul (BinaryFractionalRows.get c i) (BinaryFractionalRows.get w i)
      let a := BinaryRational.add (BinaryFractionalRows.get w i) r.weight
      let b := BinaryRational.add p.1 r.objective
      ⟨a.1,b.1,r.operations+p.2+a.2+b.2+10⟩

def totals (w c : Row N) : Totals := scan w c (List.finRange N)

/-- Only a proof-side interpretation; raw natural decoding is not executed by
any body in this module. Adjacency is passed through exactly. -/
def rawInput (adjacency : Vector (Vector Bool N) N) (w c : Row N) :
    EncodedUnitCostReplication.Input N := ⟨adjacency,decodeRow w,decodeRow c⟩

theorem scan_decode (adjacency : Vector (Vector Bool N) N) (w c : Row N)
    (is : List (Fin N)) :
    decode (scan w c is).weight=((rawInput adjacency w c).scan is).weight ∧
      decode (scan w c is).objective=((rawInput adjacency w c).scan is).objective := by
  induction is with
  | nil => exact ⟨rfl,rfl⟩
  | cons i is ih =>
      simp [scan,EncodedUnitCostReplication.Input.scan,rawInput,
        RawNonnegativeRational.Code.mulWithCost,RawNonnegativeRational.Code.addWithCost,
        BinaryFractionalRows.decodeRow,BinaryFractionalRows.get,ih.1,ih.2]

lemma scan_canonical (w c : Row N) (is : List (Fin N)) :
    Canonical (scan w c is).weight ∧ Canonical (scan w c is).objective := by
  cases is with
  | nil => exact ⟨zero_canonical,zero_canonical⟩
  | cons i is => exact ⟨add_canonical _ _,add_canonical _ _⟩

theorem scan_stored (w c : Row N) (B : ℕ)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B) (hc : ∀ i, StoredBounded (BinaryFractionalRows.get c i) B)
    (is : List (Fin N)) :
    StoredBounded (scan w c is).weight (is.length*(B+1)+1) ∧
      StoredBounded (scan w c is).objective (is.length*(2*B+1)+1) := by
  let adjacency : Vector (Vector Bool N) N := Vector.replicate N (Vector.replicate N false)
  have hd := scan_decode adjacency w c is
  have hb := EncodedUnitCostReplication.Input.scan_bounded (rawInput adjacency w c) B
    (by intro i;simpa [rawInput,decodeRow,BinaryFractionalRows.get] using stored_raw_bound (hw i))
    (by intro i;simpa [rawInput,decodeRow,BinaryFractionalRows.get] using stored_raw_bound (hc i)) is
  rw [← hd.1,← hd.2] at hb
  exact ⟨stored_of_raw (scan_canonical w c is).1 hb.1,
    stored_of_raw (scan_canonical w c is).2 hb.2⟩

def scanBound (t B : ℕ) : ℕ := t*(6144*((t+1)*(2*B+2)+1)^2+10)+1

theorem scan_charge (w c : Row N) (B : ℕ)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B) (hc : ∀ i, StoredBounded (BinaryFractionalRows.get c i) B)
    (is : List (Fin N)) : (scan w c is).operations ≤ scanBound is.length B := by
  let t := is.length
  let K := (t+1)*(2*B+2)
  have hBK : B ≤ K := by dsimp [K];nlinarith
  have aux : ∀ js : List (Fin N), js.length ≤ t →
      (scan w c js).operations ≤ js.length*(6144*(K+1)^2+10)+1 := by
    intro js
    induction js with
    | nil => intro _;simp [scan]
    | cons i js ih =>
        intro hj
        have hlen : js.length ≤ t := by simp only [List.length_cons] at hj;omega
        have ht := ih hlen
        have hb := scan_stored w c B hw hc js
        have hmul : js.length*(2*B+1) ≤ t*(2*B+1) := Nat.mul_le_mul_right _ hlen
        have hweight : js.length*(B+1)+1 ≤ K := by dsimp [K];nlinarith
        have hobjective : js.length*(2*B+1)+1 ≤ K := by dsimp [K];nlinarith
        have hwi := BinaryFractionalStepCost.stored_mono (hw i) hBK
        have hci := BinaryFractionalStepCost.stored_mono (hc i) hBK
        have hp := mul_charge hci hwi
        have hps := mul_stored_bounded (stored_raw_bound (hc i)) (stored_raw_bound (hw i))
        have hpw : StoredBounded (BinaryRational.mul (BinaryFractionalRows.get c i) (BinaryFractionalRows.get w i)).1 K :=
          BinaryFractionalStepCost.stored_mono hps (by dsimp [K];nlinarith)
        have ha := add_charge hwi (BinaryFractionalStepCost.stored_mono hb.1 hweight)
        have hd := add_charge hpw (BinaryFractionalStepCost.stored_mono hb.2 hobjective)
        simp only [scan,List.length_cons]
        nlinarith
  simpa only [scanBound,t,K] using aux is le_rfl


/-- The actual objective guard is a scan of its stored numerator bits. -/
def objectiveZero (t : Totals) : Bool × ℕ := BinaryRational.isZero t.objective

@[simp] theorem objectiveZero_spec (t : Totals) :
    (objectiveZero t).1=true ↔ (decode t.objective).num=0 := isZero_decode _

structure Normalized (N : ℕ) where
  scale : Fraction
  values : Row N
  operations : ℕ

/-- Compute the shared denominator and scale once, then each retained product. -/
def normalized (c : Row N) (t : Totals) : Normalized N :=
  let denominator := BinaryRational.mul BinaryFractionalRows.two t.objective
  let scale := BinaryRational.div t.weight denominator.1
  let rows := tabulate fun i : Fin N =>
    let q := BinaryRational.mul scale.1 (BinaryFractionalRows.get c i)
    (q.1,q.2+6)
  ⟨scale.1,rows.1,denominator.2+scale.2+rows.2+12⟩

theorem normalized_decode (adjacency : Vector (Vector Bool N) N) (w c : Row N) :
    decodeRow (normalized c (totals w c)).values =
      (rawInput adjacency w c).normalized (rawInput adjacency w c).totals := by
  have hd := scan_decode adjacency w c (List.finRange N)
  have hwdec : decode (totals w c).weight=(rawInput adjacency w c).totals.weight := hd.1
  have hcdec : decode (totals w c).objective=(rawInput adjacency w c).totals.objective := hd.2
  apply Vector.ext
  intro i hi
  simp only [normalized,EncodedUnitCostReplication.Input.normalized,
    decodeRow,BinaryFractionalRows.get,tabulate_value,Vector.getElem_ofFn,mul_decode,div_decode,
    BinaryFractionalRows.decode_two,hwdec,hcdec,rawInput]

/-- max(1,ceil q) uses a binary ceiling followed by a binary zero test. -/
def copyCount (q : Fraction) : Bits × ℕ :=
  let k := BinaryRationalCeiling.ceil q
  let z := BinaryArithmetic.isZero k.1
  (if z.1 then [true] else k.1,k.2+z.2+8)

theorem copyCount_value (q : Fraction) :
    value (copyCount q).1=max 1 (decode q).ceil := by
  have hk := (BinaryRationalCeiling.ceil_spec q).1
  have hz := (isZero_spec (BinaryRationalCeiling.ceil q).1).1
  unfold copyCount
  dsimp only
  split
  · rename_i h
    have he := hz.mp h
    rw [hk] at he
    rw [he]
    norm_num [value]
  · rename_i h
    have he : (decode q).ceil≠0 := by intro he;exact h (hz.mpr (hk.trans he))
    simp only [hk]
    exact (max_eq_right (Nat.one_le_iff_ne_zero.mpr he)).symm

theorem copyCount_length (q : Fraction) (B : ℕ) (hq : StoredBounded q B) :
    (copyCount q).1.length ≤ B+1 := by
  have h := (BinaryRationalCeiling.ceil_length_le q).trans hq.1
  unfold copyCount
  dsimp only
  split
  · simp
  · exact h.trans (Nat.le_succ B)

theorem copyCount_charge (q : Fraction) (B : ℕ) (hq : StoredBounded q B) :
    (copyCount q).2 ≤ 2048*(B+1)^2+4*(B+1)+8 := by
  have hk := BinaryRationalCeiling.ceil_charge hq
  have hl := (BinaryRationalCeiling.ceil_length_le q).trans hq.1
  have hz := (isZero_spec (BinaryRationalCeiling.ceil q).1).2
  unfold copyCount
  dsimp only
  nlinarith

def copyCounts (qs : Row N) : Vector Bits N × ℕ :=
  tabulate fun i : Fin N =>
    let k := copyCount (BinaryFractionalRows.get qs i)
    (k.1,k.2+4)

theorem copyCounts_decode (qs : Row N) :
    Vector.ofFn (fun i : Fin N => value (copyCounts qs).1[i.val]) =
      EncodedUnitCostReplication.Input.copyCounts (decodeRow qs) := by
  apply Vector.ext
  intro i hi
  simp [copyCounts,tabulate_value,EncodedUnitCostReplication.Input.copyCounts,
    decodeRow,BinaryFractionalRows.get,copyCount_value]

/-- This equality imports the existing prepared-instance clone bounds without
replacing the original graph n by the current row dimension N. -/
theorem normalized_counts_decode (adjacency : Vector (Vector Bool N) N) (w c : Row N) :
    Vector.ofFn (fun i : Fin N => value (copyCounts (normalized c (totals w c)).values).1[i.val]) =
      EncodedUnitCostReplication.Input.copyCounts
        ((rawInput adjacency w c).normalized (rawInput adjacency w c).totals) := by
  rw [copyCounts_decode,normalized_decode]

def parameterWidth (N B : ℕ) : ℕ := (N+1)*(2*B+4)

lemma parameterWidth_bounds (N B : ℕ) :
    B ≤ parameterWidth N B ∧ 2 ≤ parameterWidth N B ∧
      N*(B+1)+1 ≤ parameterWidth N B ∧ N*(2*B+1)+1 ≤ parameterWidth N B := by
  unfold parameterWidth
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem normalized_stored (w c : Row N) (B : ℕ)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B) (hc : ∀ i, StoredBounded (BinaryFractionalRows.get c i) B) :
    StoredBounded (normalized c (totals w c)).scale (3*parameterWidth N B+2) ∧
      ∀ i, StoredBounded (BinaryFractionalRows.get (normalized c (totals w c)).values i) (4*parameterWidth N B+3) := by
  let K := parameterWidth N B
  have hb := scan_stored w c B hw hc (List.finRange N)
  simp only [List.length_finRange] at hb
  have hk := parameterWidth_bounds N B
  have ht : StoredBounded (totals w c).weight K :=
    BinaryFractionalStepCost.stored_mono hb.1 hk.2.2.1
  have ho : StoredBounded (totals w c).objective K :=
    BinaryFractionalStepCost.stored_mono hb.2 hk.2.2.2
  have htwo : StoredBounded BinaryFractionalRows.two K := by
    apply BinaryFractionalStepCost.stored_mono (B := K) _ hk.2.1
    simp [StoredBounded,BinaryFractionalRows.two]
  have hd := mul_stored_bounded (stored_raw_bound htwo) (stored_raw_bound ho)
  have hs := div_stored_bounded (stored_raw_bound ht) (stored_raw_bound hd)
  have hs' : StoredBounded
      (BinaryRational.div (totals w c).weight
        (BinaryRational.mul BinaryFractionalRows.two (totals w c).objective).1).1 (3*K+2) := by
    convert hs using 1
    ring
  refine ⟨hs',?_⟩
  intro i
  have hci := BinaryFractionalStepCost.stored_mono (hc i) hk.1
  have hmul := mul_stored_bounded (stored_raw_bound hs') (stored_raw_bound hci)
  have hwidth : 3*K+2+parameterWidth N B+1=4*parameterWidth N B+3 := by
    dsimp [K]
    ring
  rw [hwidth] at hmul
  simpa only [normalized,BinaryFractionalRows.get,tabulate_value,Vector.getElem_ofFn] using hmul

def normalizedBound (N B : ℕ) : ℕ :=
  let K := parameterWidth N B
  4096*(3*K+3)^2+N*(2048*(3*K+3)^2+6)+arrayBound N+12

theorem normalized_charge (w c : Row N) (B : ℕ)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B) (hc : ∀ i, StoredBounded (BinaryFractionalRows.get c i) B) :
    (normalized c (totals w c)).operations ≤ normalizedBound N B := by
  let K := parameterWidth N B
  have hb := scan_stored w c B hw hc (List.finRange N)
  simp only [List.length_finRange] at hb
  have hk := parameterWidth_bounds N B
  have ht : StoredBounded (totals w c).weight K :=
    BinaryFractionalStepCost.stored_mono hb.1 hk.2.2.1
  have ho : StoredBounded (totals w c).objective K :=
    BinaryFractionalStepCost.stored_mono hb.2 hk.2.2.2
  have htwo : StoredBounded BinaryFractionalRows.two K := by
    apply BinaryFractionalStepCost.stored_mono (B := K) _ hk.2.1
    simp [StoredBounded,BinaryFractionalRows.two]
  have hden := mul_charge htwo ho
  have hds := mul_stored_bounded (stored_raw_bound htwo) (stored_raw_bound ho)
  have hds' : StoredBounded
      (BinaryRational.mul BinaryFractionalRows.two (totals w c).objective).1 (2*K+1) := by
    simpa only [show K+K+1=2*K+1 by ring] using hds
  have hdiv := div_charge (BinaryFractionalStepCost.stored_mono ht (by omega : K ≤ 2*K+1)) hds'
  have hs := (normalized_stored w c B hw hc).1
  have htab := tabulate_bound (fun i : Fin N =>
    let q := BinaryRational.mul (normalized c (totals w c)).scale (BinaryFractionalRows.get c i)
    (q.1,q.2+6)) (2048*(3*K+3)^2+6) (by
      intro i
      have hci := BinaryFractionalStepCost.stored_mono (hc i) (by dsimp [K];omega : B ≤ 3*K+2)
      have hmul := mul_charge hs hci
      dsimp only
      simpa only [show 3*K+2+1=3*K+3 by omega] using Nat.add_le_add_right hmul 6)
  have h1 : (K+1)^2 ≤ (3*K+3)^2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (2*K+1+1)^2 ≤ (3*K+3)^2 := Nat.pow_le_pow_left (by omega) 2
  unfold normalized normalizedBound at *
  dsimp only at *
  nlinarith

theorem copyCounts_charge (qs : Row N) (B : ℕ)
    (hq : ∀ i, StoredBounded (BinaryFractionalRows.get qs i) B) :
    (copyCounts qs).2 ≤ N*(2048*(B+1)^2+4*(B+1)+12)+arrayBound N := by
  apply tabulate_bound
  intro i
  have h := copyCount_charge (BinaryFractionalRows.get qs i) B (hq i)
  dsimp only
  omega

theorem copyCounts_lengths (qs : Row N) (B : ℕ)
    (hq : ∀ i, StoredBounded (BinaryFractionalRows.get qs i) B) (i : Fin N) :
    (copyCounts qs).1[i.val].length ≤ B+1 := by
  simpa only [copyCounts,tabulate_get] using copyCount_length (BinaryFractionalRows.get qs i) B (hq i)


end DirectedFlowCutGap.BinaryUnitCostParameters
