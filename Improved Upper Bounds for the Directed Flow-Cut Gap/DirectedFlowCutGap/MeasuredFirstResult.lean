import Mathlib.Data.List.Basic

/-! A measured first-success search that records only the tests it reaches. -/
namespace DirectedFlowCutGap.MeasuredFirstResult

def find {α : Type*} (test : α → Bool × ℕ) : List α → Option α × ℕ
  | [] => (none,1)
  | a::as =>
    let check := test a
    if check.1 then (some a,check.2+4) else
      let finish := find test as
      (finish.1,check.2+finish.2+4)

theorem find_value {α : Type*} (test : α → Bool × ℕ) (xs : List α) :
    (find test xs).1 = xs.find? (fun a => (test a).1) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    cases check : (test a).1 <;> simp [find,check,ih]

theorem find_charge {α : Type*} (test : α → Bool × ℕ) (xs : List α) {B : ℕ}
    (fits : ∀ x ∈ xs, (test x).2 ≤ B) : (find test xs).2 ≤ xs.length*(B+4)+1 := by
  induction xs with
  | nil => simp [find]
  | cons a as ih =>
    have current := fits a List.mem_cons_self
    have rest := ih (fun x member => fits x (List.mem_cons_of_mem _ member))
    simp only [find,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> omega

end DirectedFlowCutGap.MeasuredFirstResult
