import DirectedFlowCutGap.CachedScalarRead

/-! An ordered scan stops at the first successful callback. It records the
reached callback work and the binary additions of the earlier fees. -/
namespace DirectedFlowCutGap.BinaryShortScan

open CachedScalarRead (sumMeasured sum_value sum_paid)

def run {A : Type} (test : A → (Bool × ℕ) × ℕ) (fee : ℕ) : List A → (Bool × ℕ) × ℕ
  | [] =>
      let stopped := sumMeasured [fee,1]
      ((false,stopped.1),stopped.2+2)
  | a::as =>
      let step := test a
      let next := sumMeasured [fee,step.1.2]
      let work := step.2+next.2+4
      if step.1.1 then ((true,next.1),work)
      else
        let tail := run test next.1 as
        (tail.1,work+tail.2)

def reference {A : Type} (test : A → Bool × ℕ) (fee : ℕ) : List A → Bool × ℕ
  | [] => (false,fee+1)
  | a::as =>
      let step := test a
      if step.1 then (true,fee+step.2) else reference test (fee+step.2) as

@[simp] theorem run_reference {A : Type} (test : A → (Bool × ℕ) × ℕ) (fee : ℕ) (xs : List A) :
    (run test fee xs).1=reference (fun a => (test a).1) fee xs := by
  induction xs generalizing fee with
  | nil => simp only [run,reference,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
  | cons a as ih =>
      simp only [run,reference,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
      split
      · rfl
      · exact ih _

theorem reference_true {A : Type} (test : A → Bool × ℕ) (fee : ℕ) (xs : List A) :
    (reference test fee xs).1=true ↔ ∃ a ∈ xs, (test a).1=true := by
  induction xs generalizing fee with
  | nil => simp [reference]
  | cons a as ih =>
      simp only [reference,List.mem_cons,exists_eq_or_imp]
      split <;> simp_all

theorem reference_paid {A : Type} (test : A → Bool × ℕ) (fee cap : ℕ) (xs : List A)
    (fits : ∀ a ∈ xs, (test a).2 ≤ cap) : (reference test fee xs).2 ≤ fee+xs.length*cap+1 := by
  induction xs generalizing fee with
  | nil => simp only [reference,List.length_nil,Nat.zero_mul,Nat.add_zero,Nat.le_refl]
  | cons a as ih =>
      have h := fits a List.mem_cons_self
      simp only [reference,List.length_cons,Nat.add_mul,Nat.one_mul]
      split
      · omega
      · exact (ih _ (fun b hb => fits b (List.mem_cons_of_mem a hb))).trans (by omega)

private def stepBudget {R : Type*} [Semiring R] (bound child : R) : R :=
  2*(96*(bound+2)^2+4)+1+child+4

def controlBudget {R : Type*} [Semiring R] (len fee cap child : R) : R :=
  (len+1)*stepBudget (fee+len*cap+1) child

private theorem run_controlled {A : Type} (test : A → (Bool × ℕ) × ℕ) (fee cap child bound : ℕ)
    (xs : List A) (fits : fee+xs.length*cap+1 ≤ bound)
    (paid : ∀ a ∈ xs, (test a).1.2 ≤ cap ∧ (test a).2 ≤ child) :
    (run test fee xs).2 ≤ (xs.length+1)*stepBudget bound child := by
  induction xs generalizing fee with
  | nil =>
      have width : ([fee,1] : List ℕ).sum.size ≤ bound := by
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
        simp only [List.length_nil,Nat.zero_mul,Nat.add_zero] at fits
        exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans fits
      have work := sum_paid [fee,1] width
      simp only [List.length_cons,List.length_nil] at work
      simp only [run,List.length_nil,Nat.zero_add,Nat.one_mul,stepBudget]
      omega
  | cons a as ih =>
      obtain ⟨head,inside⟩ := paid a List.mem_cons_self
      let next := sumMeasured [fee,(test a).1.2]
      have nextFee : next.1=fee+(test a).1.2 := by
        simp only [next,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at fits
      have nextFits : next.1+as.length*cap+1 ≤ bound := by omega
      have width : ([fee,(test a).1.2] : List ℕ).sum.size ≤ bound := by
        simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
        exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
      have work := sum_paid [fee,(test a).1.2] width
      change next.2 ≤ 2*(96*(bound+2)^2+4)+1 at work
      have localCost : (test a).2+next.2+4 ≤ stepBudget bound child := by unfold stepBudget; omega
      have tail := ih next.1 nextFits (fun b hb => paid b (List.mem_cons_of_mem a hb))
      simp only [run,List.length_cons]
      change (if (test a).1.1 then ((true,next.1),(test a).2+next.2+4)
        else ((run test next.1 as).1,(test a).2+next.2+4+(run test next.1 as).2)).2 ≤ _
      split
      · exact localCost.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      · rw [Nat.add_mul,Nat.one_mul]
        exact (Nat.add_le_add localCost tail).trans_eq (Nat.add_comm _ _)

theorem run_paid {A : Type} (test : A → (Bool × ℕ) × ℕ) (fee cap child : ℕ) (xs : List A)
    (paid : ∀ a ∈ xs, (test a).1.2 ≤ cap ∧ (test a).2 ≤ child) :
    (run test fee xs).2 ≤ controlBudget xs.length fee cap child :=
  run_controlled test fee cap child _ xs le_rfl paid

open Polynomial in
theorem controlBudget_eval (len fee cap child : Polynomial ℕ) (x : ℕ) :
    (controlBudget len fee cap child).eval x=controlBudget (len.eval x) (fee.eval x) (cap.eval x) (child.eval x) := by
  simp only [controlBudget,stepBudget,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]

theorem controlBudget_mono {len len' fee fee' cap cap' child child' : ℕ}
    (hlen : len ≤ len') (hfee : fee ≤ fee') (hcap : cap ≤ cap') (hchild : child ≤ child') :
    controlBudget len fee cap child ≤ controlBudget len' fee' cap' child' := by
  unfold controlBudget stepBudget
  gcongr

end DirectedFlowCutGap.BinaryShortScan
