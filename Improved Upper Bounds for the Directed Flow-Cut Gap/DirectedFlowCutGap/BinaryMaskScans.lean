import DirectedFlowCutGap.BinaryIndexList
import DirectedFlowCutGap.BinaryVectorAccess
import DirectedFlowCutGap.BinaryNaturalOperations
import DirectedFlowCutGap.EncodedPreparationOutput

/-! Measure the actual two reads and label comparison of each visited
index in the port and full-fiber mask scans. The earlier fees are retained. -/
namespace DirectedFlowCutGap.BinaryMaskScans

open BinaryArithmetic EncodedUnitCostReplication
open EncodedUnitCostPreparation (Prepared)
open EncodedPortPreparation (encodePort)

private def equalNatural (a b : ℕ) : Bool × ℕ :=
  let left := BinaryNaturalView.encode a
  let right := BinaryNaturalView.encode b
  let compared := BinaryArithmetic.compare left.1 right.1
  (compared.equal,left.2+right.2+compared.steps+2)

private theorem equal_value (a b : ℕ) : (equalNatural a b).1=decide (a=b) := by
  apply Bool.eq_iff_iff.mpr
  unfold equalNatural
  dsimp only
  rw [(compare_spec _ _).2.1,BinaryNaturalView.encode_value,BinaryNaturalView.encode_value,decide_eq_true_eq]

private def compareBudget {R : Type*} [Semiring R] (B : R) : R := 32*(B+1)^2+16*(B+1)+2

private theorem equal_paid {a b B : ℕ} (ha : a.size≤B) (hb : b.size≤B) :
    (equalNatural a b).2 ≤ compareBudget B := by
  have left : (BinaryNaturalView.encode a).2 ≤ 16*(B+1)^2 := (BinaryNaturalView.encode_paid a).trans (by gcongr)
  have right : (BinaryNaturalView.encode b).2 ≤ 16*(B+1)^2 := (BinaryNaturalView.encode_paid b).trans (by gcongr)
  have compareBound := (compare_spec (BinaryNaturalView.encode a).1 (BinaryNaturalView.encode b).1).2.2
  rw [BinaryNaturalView.encode_bits a,BinaryNaturalView.encode_bits b,Nat.size_eq_bits_len,Nat.size_eq_bits_len] at compareBound
  have steps := compareBound.trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le ha hb) 1))
  have budget : 16*(B+1)^2+16*(B+1)^2=32*(B+1)^2 := by ring
  change (BinaryNaturalView.encode a).2+(BinaryNaturalView.encode b).2+
    (BinaryArithmetic.compare (BinaryNaturalView.encode a).1 (BinaryNaturalView.encode b).1).steps+2 ≤ compareBudget B
  unfold compareBudget
  rw [BinaryNaturalView.encode_bits a,BinaryNaturalView.encode_bits b]
  apply le_trans (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add left right) steps) 2)
  simp only [budget,le_refl]

private def scan {A : Type} (start : Bool) (merge : Bool → Bool → Bool)
    (per : ℕ) (test : A → Bool × ℕ) : List A → (Bool × ℕ) × ℕ
  | [] => ((start,1),1)
  | i::is =>
    let later := scan start merge per test is
    let current := test i
    let fee := BinaryNaturalOperations.add later.1.2 per
    ((merge current.1 later.1.1,fee.1),later.2+current.2+fee.2+6)

private theorem scan_legacy {A : Type} (start : Bool) (merge : Bool → Bool → Bool)
    (per : ℕ) (test : A → Bool × ℕ) (indices : List A) :
    (scan start merge per test indices).1.2=indices.length*per+1 := by
  induction indices with
  | nil => simp [scan]
  | cons i is ih =>
    simp only [scan,BinaryNaturalOperations.add_value,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem scan_paid {A : Type} (start : Bool) (merge : Bool → Bool → Bool)
    (per : ℕ) (test : A → Bool × ℕ) (indices : List A) {N B cap : ℕ}
    (count : indices.length≤N) (word : (N*per+1).size≤B) (step : per.size≤B)
    (bounded : ∀ i, (test i).2≤cap) :
    (scan start merge per test indices).2 ≤ indices.length*(cap+BinaryRawRational.budget B+10)+1 := by
  induction indices with
  | nil => simp [scan]
  | cons i is ih =>
    have shorter : is.length≤N := by simp only [List.length_cons] at count; omega
    have paid := ih shorter
    have fits : (scan start merge per test is).1.2.size≤B := by
      rw [scan_legacy]
      exact (Nat.size_le_size (Nat.add_le_add_right (Nat.mul_le_mul_right _ shorter) 1)).trans word
    have addition := BinaryNaturalOperations.add_paid fits step
    have current := bounded i
    simp only [scan,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private def coreTest {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size)
    (v : Fin n) (i : Fin out.size) : Bool × ℕ :=
  let bit := BinaryVectorAccess.read selected i
  let label := BinaryVectorAccess.read out.ports i
  let same := equalNatural label.1.val (encodePort (TerminalPorts.core v)).val
  (bit.1 && same.1,bit.2+label.2+same.2+4)

private def fiberTest {m N : ℕ} {k : Vector ℕ m} (labels : Vector (Clone k) N) (selected : Vector Bool N)
    (v : Fin m) (i : Fin N) : Bool × ℕ :=
  let bit := BinaryVectorAccess.read selected i
  let label := BinaryVectorAccess.read labels i
  let same := equalNatural label.1.1.val v.val
  (!same.1 || bit.1,bit.2+label.2+same.2+4)

def core {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size) (v : Fin n) (indices : List (Fin out.size)) :
    (Bool × ℕ) × ℕ := scan false Bool.or 20 (coreTest out selected v) indices

def fiber {m N : ℕ} {k : Vector ℕ m} (labels : Vector (Clone k) N) (selected : Vector Bool N)
    (v : Fin m) (indices : List (Fin N)) : (Bool × ℕ) × ℕ :=
  scan true Bool.and 9 (fiberTest labels selected v) indices

theorem core_value {n : ℕ} (out : Prepared n) (selected : Vector Bool out.size) (v : Fin n)
    (indices : List (Fin out.size)) : (core out selected v indices).1=out.coreScan selected v indices := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    simp only [core] at ih ⊢
    simp only [scan,coreTest,BinaryVectorAccess.read_value,equal_value,Fin.val_inj,
      BinaryNaturalOperations.add_value,ih,Prepared.coreScan]

theorem fiber_value {m N : ℕ} (k : Vector ℕ m) (labels : Vector (Clone k) N)
    (selected : Vector Bool N) (v : Fin m) (indices : List (Fin N)) :
    (fiber labels selected v indices).1=fiberScan k labels selected v indices := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    simp only [fiber] at ih ⊢
    simp only [scan,fiberTest,BinaryVectorAccess.read_value,equal_value,Fin.val_inj,
      BinaryNaturalOperations.add_value,ih,fiberScan]
    by_cases same : (labels[i.val]).1=v <;> simp [same]


private def testBudget {R : Type*} [Semiring R] (B : R) : R :=
  2*BinaryVectorAccess.budget B+compareBudget B+4

def scanBudget {R : Type*} [Semiring R] (B : R) : R :=
  testBudget B+BinaryRawRational.budget B+10

private theorem core_test_paid {n B : ℕ} (out : Prepared n) (selected : Vector Bool out.size)
    (v : Fin n) (i : Fin out.size) (array : out.size.size≤B) (label : (3*n).size≤B) :
    (coreTest out selected v i).2 ≤ testBudget B := by
  have a := BinaryVectorAccess.read_paid selected i array
  have b := BinaryVectorAccess.read_paid out.ports i array
  let stored := (BinaryVectorAccess.read out.ports i).1
  let want := encodePort (TerminalPorts.core v)
  have eq := equal_paid ((Nat.size_le_size stored.isLt.le).trans label)
    ((Nat.size_le_size want.isLt.le).trans label)
  unfold testBudget
  change (BinaryVectorAccess.read selected i).2+(BinaryVectorAccess.read out.ports i).2+
    (equalNatural stored.val want.val).2+4 ≤ _
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add a b) eq) 4).trans_eq (by ring)

private theorem fiber_test_paid {m N B : ℕ} {k : Vector ℕ m} (labels : Vector (Clone k) N)
    (selected : Vector Bool N) (v : Fin m) (i : Fin N) (array : N.size≤B) (label : m.size≤B) :
    (fiberTest labels selected v i).2 ≤ testBudget B := by
  have a := BinaryVectorAccess.read_paid selected i array
  have b := BinaryVectorAccess.read_paid labels i array
  let stored := (BinaryVectorAccess.read labels i).1.1
  have eq := equal_paid ((Nat.size_le_size stored.isLt.le).trans label)
    ((Nat.size_le_size v.isLt.le).trans label)
  unfold testBudget
  change (BinaryVectorAccess.read selected i).2+(BinaryVectorAccess.read labels i).2+
    (equalNatural stored.val v.val).2+4 ≤ _
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add a b) eq) 4).trans_eq (by ring)

theorem core_paid {n B : ℕ} (out : Prepared n) (selected : Vector Bool out.size)
    (v : Fin n) (indices : List (Fin out.size)) (count : indices.length≤out.size)
    (array : out.size.size≤B) (label : (3*n).size≤B) (fee : (out.size*20+1).size≤B)
    (step : (20 : ℕ).size≤B) :
    (core out selected v indices).2 ≤ indices.length*scanBudget B+1 := by
  exact scan_paid false Bool.or 20 (coreTest out selected v) indices count fee step
    (fun i => core_test_paid out selected v i array label)

theorem fiber_paid {m N B : ℕ} {k : Vector ℕ m} (labels : Vector (Clone k) N) (selected : Vector Bool N)
    (v : Fin m) (indices : List (Fin N)) (count : indices.length≤N) (array : N.size≤B) (label : m.size≤B)
    (fee : (N*9+1).size≤B) (step : (9 : ℕ).size≤B) :
    (fiber labels selected v indices).2 ≤ indices.length*scanBudget B+1 :=
  scan_paid true Bool.and 9 (fiberTest labels selected v) indices count fee step
    (fun i => fiber_test_paid labels selected v i array label)

end DirectedFlowCutGap.BinaryMaskScans
