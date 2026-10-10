import DirectedFlowCutGap.BinaryUnitCostParameters
import DirectedFlowCutGap.EncodedPortPreparation
import DirectedFlowCutGap.EncodedSequenceAccess

/-!
# Literal binary low masks and clipped core weights

This is the scalar/row companion to the retained raw port preparation. The
original vertex count is supplied in bits and decoded only in specifications.
The shared threshold is computed once, followed by three actual tabulations:
low-weight flags, doubled-and-clipped core weights, and full copies of the
current query-cost fields. Query padding is preserved exactly. No input weight
is replaced by the controller's positive auxiliary capacity.

The local charge composes the named Boolean-list arithmetic/copy bodies with
`tabulate`'s charged list/array construction. Port-label decoding, adjacency
materialization, shortcut searches and the representation overhead for array
access remain separate joins. The old natural-word preparation budget is not
asserted to be a bit-time bound. In particular, this module does not silently
identify original n with a later replica size or an edge-resource dimension.
-/
namespace DirectedFlowCutGap.BinaryPortWeightPreparation

open BinaryArithmetic BinaryRational BinaryFractionalRows EncodedRoundingInput
open BinaryFractionalStepCost

variable {n : ℕ}

/-- Borrow an existing numerator word; the denominator is the literal one. -/
def natural (bits : Bits) : Fraction := ⟨bits,[true],by decide⟩

@[simp] theorem natural_decode (bits : Bits) :
    decode (natural bits) = RawNonnegativeRational.Code.ofNat (value bits) := rfl

lemma natural_stored (bits : Bits) : StoredBounded (natural bits) (bits.length+1) := by
  simp [StoredBounded,natural]

/-- The zero-dimensional case follows the raw division convention 1/0 = 0. -/
def threshold (nBits : Bits) : Fraction × ℕ :=
  let d := BinaryRational.mul BinaryFractionalRows.two (natural nBits)
  let q := BinaryRational.div BinaryRational.one d.1
  (q.1,d.2+q.2+8)

theorem threshold_decode (nBits : Bits) :
    decode (threshold nBits).1 = RawNonnegativeRational.Code.one.div
      (RawNonnegativeRational.Code.ofNat (2*value nBits)) := by
  simp only [threshold,div_decode,mul_decode,decode_one,decode_two,natural_decode]
  rfl

lemma two_raw_bound : (decode BinaryFractionalRows.two).Bounded 1 := by
  norm_num [decode_two,RawNonnegativeRational.Code.ofNat,
    RawNonnegativeRational.Code.Bounded]

lemma doubled_dimension_stored (nBits : Bits) :
    StoredBounded (BinaryRational.mul BinaryFractionalRows.two (natural nBits)).1
      (nBits.length+3) := by
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    mul_stored_bounded two_raw_bound (stored_raw_bound (natural_stored nBits))

theorem threshold_stored (nBits : Bits) :
    StoredBounded (threshold nBits).1 (nBits.length+4) := by
  have hd := doubled_dimension_stored nBits
  have ho : (decode BinaryRational.one).Bounded 0 := by
    simpa only [decode_one] using RawNonnegativeRational.Code.bounded_one
  simpa only [threshold,Nat.zero_add,Nat.add_assoc] using
    div_stored_bounded ho (stored_raw_bound hd)

theorem threshold_charge (nBits : Bits) :
    (threshold nBits).2 ≤ 4096*(nBits.length+4)^2+8 := by
  have ht : StoredBounded BinaryFractionalRows.two (nBits.length+2) := by
    simp [StoredBounded,BinaryFractionalRows.two]
  have hn := stored_mono (natural_stored nBits) (by omega : nBits.length+1 ≤ nBits.length+2)
  have hm := mul_charge ht hn
  have ho : StoredBounded BinaryRational.one (nBits.length+3) := by
    simp [StoredBounded,BinaryRational.one]
  have hd := div_charge ho (doubled_dimension_stored nBits)
  change (BinaryRational.mul BinaryFractionalRows.two (natural nBits)).2+
    (BinaryRational.div BinaryRational.one
      (BinaryRational.mul BinaryFractionalRows.two (natural nBits)).1).2+8 ≤ _
  have hp := Nat.pow_le_pow_left (by omega : nBits.length+3 ≤ nBits.length+4) 2
  nlinarith

/-- Preserve the unreduced doubled fields below one; otherwise return 1/1. -/
def clipped (w : Fraction) : Fraction × ℕ :=
  let d := BinaryRational.mul BinaryFractionalRows.two w
  let c := BinaryRational.le BinaryRational.one d.1
  (if c.1 then BinaryRational.one else d.1,d.2+c.2+8)

theorem clipped_decode (w : Fraction) :
    decode (clipped w).1 = EncodedPortPreparation.clipOne
      ((RawNonnegativeRational.Code.ofNat 2).mul (decode w)) := by
  simp only [clipped]
  split <;> simp_all [EncodedPortPreparation.clipOne]

theorem clipped_stored (w : Fraction) (B : ℕ) (hw : StoredBounded w B) :
    StoredBounded (clipped w).1 (B+2) := by
  have hd : StoredBounded (BinaryRational.mul BinaryFractionalRows.two w).1 (B+2) := by
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      mul_stored_bounded two_raw_bound (stored_raw_bound hw)
  unfold clipped
  dsimp only
  split
  · simp [StoredBounded,BinaryRational.one]
  · exact hd

theorem clipped_charge (w : Fraction) (B : ℕ) (hw : StoredBounded w B) :
    (clipped w).2 ≤ 4096*(B+3)^2+8 := by
  have ht : StoredBounded BinaryFractionalRows.two (B+2) := by
    simp [StoredBounded,BinaryFractionalRows.two]
  have hm := mul_charge ht (stored_mono hw (by omega : B ≤ B+2))
  have hd : StoredBounded (BinaryRational.mul BinaryFractionalRows.two w).1 (B+2) := by
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      mul_stored_bounded two_raw_bound (stored_raw_bound hw)
  have ho : StoredBounded BinaryRational.one (B+2) := by
    simp [StoredBounded,BinaryRational.one]
  have hc := le_charge ho hd
  change (BinaryRational.mul BinaryFractionalRows.two w).2+
    (BinaryRational.le BinaryRational.one (BinaryRational.mul BinaryFractionalRows.two w).1).2+8 ≤ _
  have he : B+2+1=B+3 := by omega
  rw [he] at hm hc
  omega

/-- Literal copying of both fields, including all noncanonical zero padding. -/
def copyFraction (q : Fraction) : Fraction × ℕ :=
  let a := EncodedSequenceAccess.copyBits q.num
  let b := EncodedSequenceAccess.copyBits q.den
  (⟨a.1,b.1,by
    change 0 < value (EncodedSequenceAccess.copyBits q.den).1
    rw [(EncodedSequenceAccess.copyBits_spec q.den).1]
    exact q.den_pos⟩,
    a.2+b.2+6)

@[simp] theorem copyFraction_value (q : Fraction) : (copyFraction q).1 = q := by
  cases q
  simp [copyFraction,(EncodedSequenceAccess.copyBits_spec _).1]

theorem copyFraction_charge (q : Fraction) (B : ℕ) (hq : StoredBounded q B) :
    (copyFraction q).2 ≤ 8*B+8 := by
  have hn := (EncodedSequenceAccess.copyBits_spec q.num).2
  have hd := (EncodedSequenceAccess.copyBits_spec q.den).2
  change (EncodedSequenceAccess.copyBits q.num).2+
    (EncodedSequenceAccess.copyBits q.den).2+6 ≤ _
  rcases hq with ⟨hqnum,hqden⟩
  omega

structure Prepared (n : ℕ) where
  lowThreshold : Fraction
  low : Vector Bool n
  weights : BinaryFractionalRows.Row n
  costs : BinaryFractionalRows.Row n
  operations : ℕ

/-- Retain the shared threshold and each complete output row exactly once. -/
def prepare (nBits : Bits) (w c : BinaryFractionalRows.Row n) : Prepared n :=
  let q := threshold nBits
  let low := tabulate fun i : Fin n =>
    let t := BinaryRational.le (BinaryFractionalRows.get w i) q.1
    (t.1,t.2+4)
  let ws := tabulate fun i : Fin n =>
    let t := clipped (BinaryFractionalRows.get w i)
    (t.1,t.2+4)
  let cs := tabulate fun i : Fin n =>
    let t := copyFraction (BinaryFractionalRows.get c i)
    (t.1,t.2+4)
  ⟨q.1,low.1,ws.1,cs.1,q.2+low.2+ws.2+cs.2+12⟩

theorem prepare_low (nBits : Bits) (hn : value nBits=n)
    (adjacency : Vector (Vector Bool n) n) (w c : BinaryFractionalRows.Row n) :
    (prepare nBits w c).low = EncodedPortPreparation.lowMask
      (BinaryUnitCostParameters.rawInput adjacency w c) := by
  apply Vector.ext
  intro i hi
  simp [prepare,EncodedPortPreparation.lowMask,BinaryUnitCostParameters.rawInput,
    decodeRow,BinaryFractionalRows.get,tabulate_value,threshold_decode,hn]

theorem prepare_weight (nBits : Bits) (adjacency : Vector (Vector Bool n) n)
    (w c : BinaryFractionalRows.Row n) (i : Fin n) :
    decode (BinaryFractionalRows.get (prepare nBits w c).weights i) =
      EncodedPortPreparation.preparedWeightCode
        (BinaryUnitCostParameters.rawInput adjacency w c) (.inl i) := by
  simp [prepare,BinaryFractionalRows.get,tabulate_value,clipped_decode,
    EncodedPortPreparation.preparedWeightCode,BinaryUnitCostParameters.rawInput,decodeRow]

/-- Stronger than equality of rational values: the original cost bytes survive. -/
theorem prepare_cost (nBits : Bits) (w c : BinaryFractionalRows.Row n) (i : Fin n) :
    BinaryFractionalRows.get (prepare nBits w c).costs i = BinaryFractionalRows.get c i := by
  simp [prepare,BinaryFractionalRows.get,tabulate_value]

theorem prepare_stored (nBits : Bits) (w c : BinaryFractionalRows.Row n) (B : ℕ)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B)
    (hc : ∀ i, StoredBounded (BinaryFractionalRows.get c i) B) :
    StoredBounded (prepare nBits w c).lowThreshold (nBits.length+4) ∧
    (∀ i, StoredBounded (BinaryFractionalRows.get (prepare nBits w c).weights i) (B+2)) ∧
    (∀ i, StoredBounded (BinaryFractionalRows.get (prepare nBits w c).costs i) B) := by
  refine ⟨threshold_stored nBits,?_,?_⟩
  · intro i
    simpa only [prepare,BinaryFractionalRows.get,tabulate_get] using
      clipped_stored (BinaryFractionalRows.get w i) B (hw i)
  · intro i
    rw [prepare_cost]
    exact hc i

def preparationBound (n D B : ℕ) : ℕ :=
  4096*(D+4)^2+n*(6144*(B+D+5)^2+8*B+28)+3*arrayBound n+20

theorem prepare_charge (nBits : Bits) (w c : BinaryFractionalRows.Row n) (B : ℕ)
    (hw : ∀ i, StoredBounded (BinaryFractionalRows.get w i) B)
    (hc : ∀ i, StoredBounded (BinaryFractionalRows.get c i) B) :
    (prepare nBits w c).operations ≤ preparationBound n nBits.length B := by
  let K := B+nBits.length+4
  have hBK : B ≤ K := by dsimp [K];omega
  have hqK : nBits.length+4 ≤ K := by dsimp [K];omega
  have hq := threshold_charge nBits
  have hl := tabulate_bound (fun i : Fin n =>
    let t := BinaryRational.le (BinaryFractionalRows.get w i) (threshold nBits).1
    (t.1,t.2+4)) (2048*(K+1)^2+4) (by
      intro i
      exact Nat.add_le_add_right (le_charge (stored_mono (hw i) hBK)
        (stored_mono (threshold_stored nBits) hqK)) 4)
  have hws := tabulate_bound (fun i : Fin n =>
    let t := clipped (BinaryFractionalRows.get w i)
    (t.1,t.2+4)) (4096*(K+1)^2+12) (by
      intro i
      have h := clipped_charge (BinaryFractionalRows.get w i) B (hw i)
      have hb : B+3 ≤ K+1 := by dsimp [K];omega
      have hs := Nat.pow_le_pow_left hb 2
      dsimp only
      nlinarith)
  have hcs := tabulate_bound (fun i : Fin n =>
    let t := copyFraction (BinaryFractionalRows.get c i)
    (t.1,t.2+4)) (8*B+12) (by
      intro i
      have h := copyFraction_charge (BinaryFractionalRows.get c i) B (hc i)
      dsimp only
      omega)
  change (threshold nBits).2+_+_+_+12 ≤ _
  dsimp only [preparationBound,K] at *
  nlinarith

end DirectedFlowCutGap.BinaryPortWeightPreparation
