import DirectedFlowCutGap.EncodedSequenceAccess

/-!
# Polynomial overhead for literal movement of retained finite values

This is the common copying ingredient, not a source-body or whole-algorithm
certificate. A reached body must still supply its actual movement trace,
structural/binary work bound, and a bound on ALL moved values, including retained
frames and intermediates. The procedures below literally copy every supplied
value with CopyExec. They never execute an arbitrary host callback as a priced
primitive. The final congruence theorem merely states that an identical copied
argument leaves a separately supplied monadic computation unchanged.
-/
namespace DirectedFlowCutGap.EncodedCopyOverhead
open EncodedSequenceAccess

/-- Copy every retained argument once, including each argument-list constructor. -/
def copyInputs : List Value → List Value × ℕ
  | [] => ([],1)
  | x::xs =>
      let h := EncodedSequenceAccess.copy x
      let t := copyInputs xs
      (h.1::t.1,h.2+t.2+4)

inductive InputsExec : List Value → List Value → ℕ → Prop
  | nil : InputsExec [] [] 1
  | cons (x y : Value) (xs ys : List Value) (q r : ℕ) :
      CopyExec x y q → InputsExec xs ys r →
      InputsExec (x::xs) (y::ys) (q+r+4)

theorem copyInputs_exec (xs : List Value) :
    InputsExec xs (copyInputs xs).1 (copyInputs xs).2 := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons x _ xs _ _ _ (copy_exec x) ih

theorem InputsExec.result {xs ys : List Value} {q : ℕ}
    (h : InputsExec xs ys q) : ys = (copyInputs xs).1 ∧ q = (copyInputs xs).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons x y xs ys q r hx ht ih =>
      have hh := hx.result
      constructor <;> simp only [copyInputs,hh.1,hh.2,ih.1,ih.2]

@[simp] theorem copyInputs_value (xs : List Value) : (copyInputs xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [copyInputs,(copy_spec x).1,ih]

theorem copyInputs_bound (xs : List Value) (S : ℕ)
    (h : ∀ x ∈ xs, x.size ≤ S) :
    (copyInputs xs).2 ≤ 4*(S+1)*xs.length+1 := by
  induction xs with
  | nil => simp [copyInputs]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [copyInputs,(copy_spec x).2,List.length_cons]
      nlinarith

theorem InputsExec.cost {xs ys : List Value} {q : ℕ}
    (run : InputsExec xs ys q) (S : ℕ) (h : ∀ x ∈ xs, x.size ≤ S) :
    q ≤ 4*(S+1)*xs.length+1 := by
  rw [run.result.2]
  exact copyInputs_bound xs S h

/-- One finite pack per reached structural event. This procedure copies those
packs; it does not assert that an arbitrary supplied trace came from a program. -/
def copyTrace : List (List Value) → List (List Value) × ℕ
  | [] => ([],1)
  | xs::rest =>
      let x := copyInputs xs
      let t := copyTrace rest
      (x.1::t.1,x.2+t.2+4)

inductive TraceExec : List (List Value) → List (List Value) → ℕ → Prop
  | nil : TraceExec [] [] 1
  | cons (xs ys : List Value) (rest out : List (List Value)) (q r : ℕ) :
      InputsExec xs ys q → TraceExec rest out r →
      TraceExec (xs::rest) (ys::out) (q+r+4)

theorem copyTrace_exec (trace : List (List Value)) :
    TraceExec trace (copyTrace trace).1 (copyTrace trace).2 := by
  induction trace with
  | nil => exact .nil
  | cons xs rest ih => exact .cons xs _ rest _ _ _ (copyInputs_exec xs) ih

theorem TraceExec.result {trace out : List (List Value)} {q : ℕ}
    (h : TraceExec trace out q) : out = (copyTrace trace).1 ∧ q = (copyTrace trace).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons xs ys rest out q r hx ht ih =>
      have hh := hx.result
      constructor <;> simp only [copyTrace,hh.1,hh.2,ih.1,ih.2]

@[simp] theorem copyTrace_value (trace : List (List Value)) :
    (copyTrace trace).1 = trace := by
  induction trace with
  | nil => rfl
  | cons xs rest ih => simp only [copyTrace,copyInputs_value,ih]

theorem copyTrace_bound (trace : List (List Value)) (A S : ℕ)
    (h : ∀ xs ∈ trace, xs.length ≤ A ∧ ∀ x ∈ xs, x.size ≤ S) :
    (copyTrace trace).2 ≤ (4*A+5)*(S+1)*trace.length+1 := by
  induction trace with
  | nil => simp [copyTrace]
  | cons xs rest ih =>
      have hx := h xs (by simp)
      have hc := copyInputs_bound xs S hx.2
      have hl := Nat.mul_le_mul_left (4*(S+1)) hx.1
      have ht := ih (fun ys hy => h ys (by simp [hy]))
      simp only [copyTrace,List.length_cons]
      nlinarith

/-- Add literal movement cost to an independently certified body cost. The
caller must bind the trace to its execution and prove the global size invariant;
this theorem cannot turn arbitrary host evaluation into a certified body. -/
theorem total_bound (trace : List (List Value)) (A S work base : ℕ)
    (h : ∀ xs ∈ trace, xs.length ≤ A ∧ ∀ x ∈ xs, x.size ≤ S)
    (hlen : trace.length ≤ work) (hbase : base ≤ work) :
    base+(copyTrace trace).2 ≤ (4*A+6)*(S+1)*(work+1) := by
  have hc := copyTrace_bound trace A S h
  have hl := Nat.mul_le_mul_left ((4*A+5)*(S+1)) hlen
  nlinarith

/-- Copying is pure and preserves the entire supplied monadic computation,
including its random-source state. This does not price the body itself. -/
theorem copied_arguments_preserve {M : Type → Type} {α : Type}
    (body : List Value → M α) (xs : List Value) :
    body (copyInputs xs).1 = body xs := by
  rw [copyInputs_value]

end DirectedFlowCutGap.EncodedCopyOverhead
