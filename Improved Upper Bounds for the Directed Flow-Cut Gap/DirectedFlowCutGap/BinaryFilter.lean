import DirectedFlowCutGap.CachedScalarRead

/-! Filter in the input order, recording reached predicate work and binary
additions of the prior fees. Retained list cells are collected and reversed. -/
namespace DirectedFlowCutGap.BinaryFilter

open CachedScalarRead (sumMeasured sum_value sum_paid)

def reference {A : Type*} (test : A → Bool × ℕ) (kept : List A) (fee : ℕ) : List A → List A × ℕ
  | [] => (kept.reverse,fee+1)
  | x::xs =>
    let keep := test x
    reference test (if keep.1 then x::kept else kept) (fee+keep.2+8) xs

private def filter {A : Type*} (test : A → (Bool × ℕ) × ℕ) (kept : List A) (fee : ℕ) :
    List A → (List A × ℕ) × ℕ
  | [] =>
    let stop := sumMeasured [fee,1]
    ((kept.reverse,stop.1),stop.2+4*kept.length+2)
  | x::xs =>
    let keep := test x
    let next := sumMeasured [fee,keep.1.2,8]
    let tail := filter test (if keep.1.1 then x::kept else kept) next.1 xs
    (tail.1,keep.2+next.2+4+tail.2)

private theorem filter_reference {A : Type*} (test : A → (Bool × ℕ) × ℕ) (kept : List A)
    (fee : ℕ) (xs : List A) : (filter test kept fee xs).1=reference (fun x => (test x).1) kept fee xs := by
  induction xs generalizing fee kept with
  | nil => simp only [filter,reference,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
  | cons x xs ih =>
    simp only [filter,reference,ih,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]

def run {A : Type*} (test : A → (Bool × ℕ) × ℕ) (xs : List A) : (List A × ℕ) × ℕ := filter test [] 0 xs

theorem run_reference {A : Type*} (test : A → (Bool × ℕ) × ℕ) (xs : List A) :
    (run test xs).1=reference (fun x => (test x).1) [] 0 xs := filter_reference test [] 0 xs

private def stepBudget {R : Type*} [Semiring R] (total child : R) : R :=
  3*(96*(total+2)^2+4)+1+child+8

def controlBudget {R : Type*} [Semiring R] (m fee child : R) : R :=
  (m+1)*stepBudget (m*(fee+8)+1) child

private theorem filter_paid {A : Type*} (test : A → (Bool × ℕ) × ℕ) (kept : List A) (fee cap child total : ℕ)
    (xs : List A) (fits : fee+xs.length*(cap+8)+1≤total)
    (each : ∀ x ∈ xs, (test x).1.2≤cap ∧ (test x).2≤child) :
    (filter test kept fee xs).2 ≤ (xs.length+1)*stepBudget total child+4*kept.length := by
  induction xs generalizing fee kept with
  | nil =>
    have width : ([fee,1] : List ℕ).sum.size ≤ total := by
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
      simp only [List.length_nil,Nat.zero_mul,Nat.add_zero] at fits
      exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans fits
    have work := sum_paid [fee,1] width
    simp only [List.length_cons,List.length_nil] at work
    simp only [filter,List.length_nil,Nat.zero_add,Nat.one_mul,stepBudget]
    omega
  | cons x xs ih =>
    obtain ⟨feeCap,workCap⟩ := each x List.mem_cons_self
    let next := sumMeasured [fee,(test x).1.2,8]
    let carry := if (test x).1.1 then x::kept else kept
    have newFee : next.1=fee+(test x).1.2+8 := by
      simp only [next,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
    have newKept : carry.length ≤ kept.length+1 := by
      unfold carry
      split <;> simp only [List.length_cons,Nat.le_refl,Nat.le_succ]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at fits
    have nextFits : next.1+xs.length*(cap+8)+1 ≤ total := by omega
    have width : ([fee,(test x).1.2,8] : List ℕ).sum.size ≤ total := by
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
      exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have work := sum_paid [fee,(test x).1.2,8] width
    change next.2≤3*(96*(total+2)^2+4)+1 at work
    have tail := ih carry next.1 nextFits (fun y hy => each y (List.mem_cons_of_mem x hy))
    simp only [Nat.add_mul,Nat.one_mul] at tail
    have step : (test x).2+next.2+4+4 ≤ stepBudget total child := by unfold stepBudget; omega
    change (test x).2+next.2+4+(filter test carry next.1 xs).2 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem run_paid {A : Type*} (test : A → (Bool × ℕ) × ℕ) (xs : List A) (cap child : ℕ)
    (each : ∀ x ∈ xs, (test x).1.2≤cap ∧ (test x).2≤child) :
    (run test xs).2 ≤ controlBudget xs.length cap child := by
  simpa only [run,controlBudget,Nat.zero_add,List.length_nil,Nat.mul_zero,Nat.add_zero] using
    filter_paid test [] 0 cap child (xs.length*(cap+8)+1) xs (by simp) each

theorem controlBudget_mono {m m' f f' c c' : ℕ} (hm : m≤m') (hf : f≤f') (hc : c≤c') :
    controlBudget m f c ≤ controlBudget m' f' c' := by
  unfold controlBudget stepBudget
  gcongr

open Polynomial in
theorem controlBudget_eval (m fee child : Polynomial ℕ) (x : ℕ) :
    (controlBudget m fee child).eval x=controlBudget (m.eval x) (fee.eval x) (child.eval x) := by
  simp only [controlBudget,stepBudget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

end DirectedFlowCutGap.BinaryFilter
