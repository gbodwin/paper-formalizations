import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Aesop

/-! Computable rational distance values. `none` denotes unreachable, never zero.
The minimum fold is a finite executable loop; no classical choice is used. -/
namespace LightEFTSpanners.RationalDistance

def Below (a : Option ℚ) (b : ℚ) : Prop := ∃ x, a = some x ∧ x ≤ b

def best : Option ℚ → Option ℚ → Option ℚ
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

@[simp] theorem below_none (b : ℚ) : ¬Below none b := by simp [Below]
@[simp] theorem below_some (a b : ℚ) : Below (some a) b ↔ a ≤ b := by simp [Below]

 theorem below_best (a b : Option ℚ) (c : ℚ) :
    Below (best a b) c ↔ Below a c ∨ Below b c := by
  cases a <;> cases b <;> simp [best, min_le_iff]

 theorem below_fold (l : List (Option ℚ)) (a : Option ℚ) (b : ℚ) :
    Below (l.foldr best a) b ↔ Below a b ∨ ∃ x∈l, Below x b := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.foldr_cons, below_best, ih, List.mem_cons]; aesop

 theorem below_map_add (a : Option ℚ) (w b : ℚ) :
    Below (a.map (w + ·)) b ↔ ∃ x, a = some x ∧ w+x≤b := by
  cases a <;> simp [Below]

 theorem below_mono {a : Option ℚ} {b c : ℚ} (h : Below a b) (hbc : b≤c) :
    Below a c := by obtain ⟨x,hx,h⟩ := h; exact ⟨x,hx,h.trans hbc⟩

 def test (a : Option ℚ) (b : ℚ) : Bool :=
  match a with | none => false | some x => decide (x≤b)

 @[simp] theorem test_eq_true (a : Option ℚ) (b : ℚ) : test a b=true ↔ Below a b := by
  cases a <;> simp [test]
end LightEFTSpanners.RationalDistance
