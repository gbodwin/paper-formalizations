import DirectedFlowCutGap.BinaryWeightedSampling
import DirectedFlowCutGap.EncodedSequenceAccess

/-!
# Fixed structural execution of retained weighted-mass preparation

These are derivations for the actual scale, encode, total-sum and prepare
bodies. The only scalar calls in their rules are the existing fixed binary
addCanonical and mulCanonical implementations. Label movement uses the same
literal BitsCopyExec relation as retained sequence access. There is no rule
for evaluating an arbitrary host function or an input-specific result literal.

The model borrows retained list tails and Fraction fields when destructuring
records. Constructors and literal label copies are charged here; the common
representation simulation must price moving borrowed references. The finite
Value encodings below are proof-side size observations, never freshly executed
maps hidden in a callback. Named scalar bodies keep their existing Boolean/list
semantics and charges. This local body join does not by itself prove the whole
sampler/controller runtime or a native compiler/allocator theorem.
-/
namespace DirectedFlowCutGap.BinaryWeightedPreparationExec
open BinaryArithmetic BinaryWeightedMasses BinaryWeightedSampling
open EncodedSequenceAccess

theorem label_copy_eq (bits : Bits) :
    BinaryWeightedChoice.copyBits bits = EncodedSequenceAccess.copyBits bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [BinaryWeightedChoice.copyBits,EncodedSequenceAccess.copyBits,ih]

theorem label_copy_exec (bits : Bits) :
    BitsCopyExec bits (BinaryWeightedChoice.copyBits bits).1
      (BinaryWeightedChoice.copyBits bits).2 := by
  rw [label_copy_eq]
  exact copyBits_exec bits

theorem label_copy_result {bits copied : Bits} {q : ℕ}
    (h : BitsCopyExec bits copied q) :
    copied = (BinaryWeightedChoice.copyBits bits).1 ∧
      q = (BinaryWeightedChoice.copyBits bits).2 := by
  simpa only [label_copy_eq] using h.result

/-- Actual retained-list recursion, one fixed product and one literal copy. -/
inductive ScaleExec (d : Bits) : MassList → MassList → ℕ → Prop
  | nil : ScaleExec d [] [] 1
  | cons (label mass : Bits) (xs tail : MassList) (q : ℕ) (copied : Bits) (c : ℕ) :
      ScaleExec d xs tail q → BitsCopyExec label copied c →
      ScaleExec d ((label,mass)::xs)
        ((copied,(mulCanonical d mass).1)::tail)
        (q+(mulCanonical d mass).2+c+12)

theorem scale_exec (d : Bits) (xs : MassList) :
    ScaleExec d xs (scale d xs).1 (scale d xs).2 := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      rcases x with ⟨label,mass⟩
      exact .cons label mass xs _ _ _ _ ih (label_copy_exec label)

theorem ScaleExec.result {d : Bits} {xs out : MassList} {q : ℕ}
    (h : ScaleExec d xs out q) : out = (scale d xs).1 ∧ q = (scale d xs).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons label mass xs tail q copied c _ hc ih =>
      have hh := label_copy_result hc
      constructor
      · simp only [scale,ih.1,hh.1]
      · simp only [scale,ih.2,hh.2]

/-- Two fixed products, the actual tail rescaling, and the actual head copy. -/
inductive EncodeExec : Input → Bits → MassList → ℕ → Prop
  | nil : EncodeExec [] [true] [] 1
  | cons (label : Bits) (amount : BinaryRational.Fraction) (xs : Input)
      (d : Bits) (tail scaled : MassList) (q r : ℕ) (copied : Bits) (c : ℕ) :
      EncodeExec xs d tail q → ScaleExec amount.den tail scaled r →
      BitsCopyExec label copied c →
      EncodeExec ((label,amount)::xs) (mulCanonical amount.den d).1
        ((copied,(mulCanonical amount.num d).1)::scaled)
        (q+(mulCanonical amount.den d).2+(mulCanonical amount.num d).2+r+c+16)

theorem encode_exec (xs : Input) :
    EncodeExec xs (encode xs).denominator (encode xs).masses (encode xs).operations := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      rcases x with ⟨label,amount⟩
      exact .cons label amount xs _ _ _ _ _ _ _ ih
        (scale_exec amount.den (encode xs).masses) (label_copy_exec label)

theorem EncodeExec.result {xs : Input} {d : Bits} {masses : MassList} {q : ℕ}
    (h : EncodeExec xs d masses q) :
    d = (encode xs).denominator ∧ masses = (encode xs).masses ∧ q = (encode xs).operations := by
  induction h with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons label amount xs d tail scaled q r copied c _ hs hc ih =>
      have ht := hs.result
      have hl := label_copy_result hc
      constructor
      · simp only [encode,ih.1]
      constructor
      · simp only [encode,ht.1,hl.1,ih.1,ih.2.1]
      · simp only [encode,ht.2,hl.2,ih.1,ih.2.1,ih.2.2]

/-- One actual binary addition at each visited mass-list node. -/
inductive SumExec : MassList → Bits → ℕ → Prop
  | nil : SumExec [] [] 1
  | cons (label mass : Bits) (xs : MassList) (out : Bits) (q : ℕ) :
      SumExec xs out q →
      SumExec ((label,mass)::xs) (addCanonical mass out).1
        (q+(addCanonical mass out).2+8)

theorem sum_exec (xs : MassList) : SumExec xs (sumMass xs).1 (sumMass xs).2 := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons x.1 x.2 xs _ _ ih

theorem SumExec.result {xs : MassList} {out : Bits} {q : ℕ}
    (h : SumExec xs out q) : out = (sumMass xs).1 ∧ q = (sumMass xs).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons label mass xs out q _ ih =>
      constructor
      · simp only [sumMass,ih.1]
      · simp only [sumMass,ih.1,ih.2]

/-- One encode and one total scan compose the exact prepared record. -/
inductive PrepareExec (xs : Input) : Bits → MassList → Bits → ℕ → Prop
  | make (d : Bits) (masses : MassList) (total : Bits) (q r : ℕ) :
      EncodeExec xs d masses q → SumExec masses total r →
      PrepareExec xs d masses total (q+r+8)

theorem prepare_exec (xs : Input) :
    PrepareExec xs (prepare xs).denominator (prepare xs).masses
      (prepare xs).total (prepare xs).operations :=
  .make _ _ _ _ _ (encode_exec xs) (sum_exec (encode xs).masses)

theorem PrepareExec.result {xs : Input} {d total : Bits} {masses : MassList} {q : ℕ}
    (h : PrepareExec xs d masses total q) :
    d = (prepare xs).denominator ∧ masses = (prepare xs).masses ∧
      total = (prepare xs).total ∧ q = (prepare xs).operations := by
  cases h with
  | make q r he hs =>
      have hh := he.result
      have ht := hs.result
      exact ⟨hh.1,hh.2.1,by simpa only [prepare,hh.2.1] using ht.1,
        by simp only [prepare,hh.2.1,hh.2.2,ht.2]⟩

/-- An execution derivation's cost, not an arbitrary supplied annotation. -/
theorem PrepareExec.cost {xs : Input} {d total : Bits} {masses : MassList} {q : ℕ}
    (run : PrepareExec xs d masses total q) (B C : ℕ)
    (h : ∀ x ∈ xs, x.1.length ≤ C ∧ BinaryRational.StoredBounded x.2 B) :
    q ≤ preparationBound xs.length B C := by
  rw [run.result.2.2.2]
  exact prepare_cost xs B C h

/-- These finite encodings observe retained fields; no runtime map is added. -/
def massValue (x : Bits × Bits) : Value := .pair (.word x.1) (.word x.2)

def massesValue (xs : MassList) : Value := sequence (xs.map massValue)

def inputValue (x : Bits × BinaryRational.Fraction) : Value :=
  .pair (.word x.1) (.pair (.word x.2.num) (.word x.2.den))

def inputsValue (xs : Input) : Value := sequence (xs.map inputValue)

def preparedValue (d : Bits) (masses : MassList) (total : Bits) : Value :=
  .pair (.word d) (.pair (massesValue masses) (.word total))

theorem masses_size (xs : MassList) (B C : ℕ)
    (h : ∀ x ∈ xs, x.1.length ≤ C ∧ x.2.length ≤ B) :
    (massesValue xs).size ≤ xs.length*(C+B+4)+1 := by
  have hh : ∀ x ∈ xs.map massValue, x.size ≤ C+B+3 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    obtain ⟨hl,hm⟩ := h y hy
    simp only [massValue,Value.size]
    omega
  simpa only [massesValue,List.length_map] using sequence_size_bound hh

theorem inputs_size (xs : Input) (B C : ℕ)
    (h : ∀ x ∈ xs, x.1.length ≤ C ∧ BinaryRational.StoredBounded x.2 B) :
    (inputsValue xs).size ≤ xs.length*(C+2*B+6)+1 := by
  have hh : ∀ x ∈ xs.map inputValue, x.size ≤ C+2*B+5 := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    obtain ⟨hl,hn,hd⟩ := h y hy
    simp only [inputValue,Value.size]
    omega
  simpa only [inputsValue,List.length_map] using sequence_size_bound hh

def preparationSize (k B C : ℕ) : ℕ := k*(C+k*B+2*B+6)+7

/-- Actual padded denominator, every mass word, every copied label and the
actual accumulated total are included in the retained result-size bound. -/
theorem prepare_size (xs : Input) (B C : ℕ)
    (h : ∀ x ∈ xs, x.1.length ≤ C ∧ BinaryRational.StoredBounded x.2 B) :
    (preparedValue (prepare xs).denominator (prepare xs).masses (prepare xs).total).size ≤
      preparationSize xs.length B C := by
  have hd := (encode_stored xs B (fun x hx => (h x hx).2)).1
  have hw := prepare_widths xs B C h
  have hm := masses_size (prepare xs).masses (xs.length*B+1) C hw.2
  have hlen : (prepare xs).masses.length = xs.length := encode_length xs
  rw [hlen] at hm
  change (prepare xs).denominator.length ≤ xs.length*B+1 at hd
  simp only [preparedValue,Value.size,preparationSize]
  nlinarith [hw.1]

theorem PrepareExec.size {xs : Input} {d total : Bits} {masses : MassList} {q : ℕ}
    (run : PrepareExec xs d masses total q) (B C : ℕ)
    (h : ∀ x ∈ xs, x.1.length ≤ C ∧ BinaryRational.StoredBounded x.2 B) :
    (preparedValue d masses total).size ≤ preparationSize xs.length B C := by
  rw [run.result.1,run.result.2.1,run.result.2.2.1]
  exact prepare_size xs B C h

end DirectedFlowCutGap.BinaryWeightedPreparationExec
